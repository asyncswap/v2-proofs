// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";
import {RadixPriceTree} from "./RadixPriceTree.sol";

/// @title AsyncFiller
/// @notice Per-pool order storage and the price-time-priority book.
/// @dev Spec: `AsyncSwapSpec/Order.lean` (`Order`, `priceKey`, `MIN/MAX_PRIORITY_FEE`), `Priority.lean`
///      (bid first, then FIFO; reprice re-enters last; the matched level is the best price),
///      `Book.lean` (`create`, `recordPriorityFee`, `fill`, `cancel`, `updatePrice` and the escrow
///      invariant), `Reduce.lean` (`reduce`: partial-fill accounting), `Bounds.lean` (`uint64` sequence and
///      bid, `uint128` keys).
///
///      The book is two `RadixPriceTree`s of price keys (bids: higher is better; asks: lower is better). Each
///      price level is a queue of order ids kept in sequence order, plus — in `PriorityFee` mode — a
///      `RadixPriceTree` of `_priorityKey(fee, sequence) = (fee << 64) | (maxUint64 − sequence)` so that
///      `best(true)` is the highest bid and, among equal bids, the earliest sequence.
library AsyncFiller {
    using RadixPriceTree for RadixPriceTree.Tree;

    uint256 internal constant PRICE_SCALE = 1e18;
    uint64 internal constant MIN_PRIORITY_FEE = 100_000; // $0.10 in six-decimal USDC
    uint64 internal constant MAX_PRIORITY_FEE = type(uint64).max;
    uint128 internal constant MAX_PRICE_KEY = type(uint128).max;

    enum OrderingMode {
        FIFO,
        PriorityFee
    }

    /// @dev `amountIn == 0` means "no such order". The bid is always escrowed (the hook mints its claim in the
    ///      same `beforeSwap` that creates the order), so the model's `priorityFeeEscrowed` flag is constant.
    struct OrderInfo {
        address owner;
        bool zeroForOne;
        uint64 priorityFee;
        uint64 sequence;
        uint128 priceKey;
        uint128 priorityKey;
        uint256 amountIn;
        uint256 amountOutMin;
        bytes32 previous;
        bytes32 next;
    }

    struct PriceLevel {
        bytes32 head;
        bytes32 tail;
        uint256 count;
        RadixPriceTree.Tree priorityOrders;
        mapping(uint128 => bytes32) priorityOrderIds;
    }

    struct Book {
        OrderingMode orderingMode;
        uint64 nextSequence;
        uint256 openOrders;
        RadixPriceTree.Tree bids;
        RadixPriceTree.Tree asks;
        mapping(uint128 => PriceLevel) bidLevels;
        mapping(uint128 => PriceLevel) askLevels;
    }

    struct State {
        mapping(bytes32 => OrderInfo) orders;
        mapping(address => mapping(address => bool)) isExecutor;
        Book book;
    }

    error OrderExists(bytes32 id);
    error OrderNotFound(bytes32 id);
    error ZeroAmountIn();
    error ZeroAmountOutMin();
    error PriorityFeeNotAllowed();
    error PriorityFeeTooLow(uint256 priorityFee);
    error PriorityFeeTooHigh(uint256 priorityFee);
    error NotOrderOwner(bytes32 id);
    error BookNotEmpty();

    /// @dev A *buy* spends the numeraire (currency1) for currency0, i.e. `zeroForOne == false`.
    function isBuy(bool zeroForOne) internal pure returns (bool) {
        return !zeroForOne;
    }

    /* ─────────────────────────────── transitions ─────────────────────────────── */

    /// @dev `Book.create` guards and storage effect (the claim mint is the hook's).
    function addOrder(
        State storage self,
        bytes32 id,
        address owner,
        bool zeroForOne,
        uint256 amountIn,
        uint256 amountOutMin,
        uint256 priorityFee
    ) internal returns (uint64 sequence) {
        if (amountIn == 0) revert ZeroAmountIn();
        if (amountOutMin == 0) revert ZeroAmountOutMin();
        OrderInfo storage info = self.orders[id];
        if (info.amountIn != 0) revert OrderExists(id);

        Book storage book = self.book;
        if (book.orderingMode == OrderingMode.FIFO) {
            if (priorityFee != 0) revert PriorityFeeNotAllowed();
        } else if (priorityFee < MIN_PRIORITY_FEE) {
            revert PriorityFeeTooLow(priorityFee);
        }
        if (priorityFee > MAX_PRIORITY_FEE) revert PriorityFeeTooHigh(priorityFee);

        sequence = ++book.nextSequence;
        info.owner = owner;
        info.zeroForOne = zeroForOne;
        info.amountIn = amountIn;
        info.amountOutMin = amountOutMin;
        info.priorityFee = uint64(priorityFee);
        info.sequence = sequence;
        info.priceKey = priceKey(isBuy(zeroForOne), amountIn, amountOutMin);
        book.openOrders += 1;
        _append(self, id, info);
    }

    /// @dev `eraseOrder`: leave the book and delete the record. Returns a memory copy of what was stored.
    function close(State storage self, bytes32 id) internal returns (OrderInfo memory closed) {
        OrderInfo storage info = self.orders[id];
        if (info.amountIn == 0) revert OrderNotFound(id);
        closed = info;
        _remove(self, id, info);
        delete self.orders[id];
        self.book.openOrders -= 1;
    }

    /// @dev `Book.updatePrice`: maker-only, pure storage change; the order re-enters its level last
    ///      (`Priority.lean` `reprice_sequence_last`).
    function updatePrice(State storage self, bytes32 id, address caller, uint256 newAmountOutMin)
        internal
        returns (uint64 sequence)
    {
        OrderInfo storage info = self.orders[id];
        if (info.amountIn == 0) revert OrderNotFound(id);
        if (caller != info.owner) revert NotOrderOwner(id);
        if (newAmountOutMin == 0) revert ZeroAmountOutMin();
        _remove(self, id, info);
        info.amountOutMin = newAmountOutMin;
        info.priceKey = priceKey(isBuy(info.zeroForOne), info.amountIn, newAmountOutMin);
        sequence = ++self.book.nextSequence;
        info.sequence = sequence;
        _append(self, id, info);
    }

    /// @dev The storage half of `_reduceAfterMatch` / `_settleMatchedPriorityFee` (`Reduce.lean`
    ///      `Order.reduce`, `donatedFee`): consume `used` input, credit `received` output against the
    ///      outstanding minimum, donate the pro-rata share of the bid. Closes the order when either remaining
    ///      amount hits zero. A still-open order keeps its sequence; its price key is recomputed and the order
    ///      moves level only if the key changed.
    function reduce(State storage self, bytes32 id, uint256 used, uint256 received)
        internal
        returns (bool closed, uint256 remainingIn, uint256 donatedFee, uint256 remainingFee)
    {
        OrderInfo storage info = self.orders[id];
        uint256 oldIn = info.amountIn;
        if (oldIn == 0) revert OrderNotFound(id);
        uint256 oldMin = info.amountOutMin;
        uint64 oldFee = info.priorityFee;

        remainingIn = oldIn - used;
        uint256 remainingMin = received >= oldMin ? 0 : oldMin - received;
        donatedFee = Math.mulDiv(oldFee, used, oldIn);
        remainingFee = oldFee - donatedFee;

        if (remainingIn == 0 || remainingMin == 0) {
            closed = true;
            _remove(self, id, info);
            delete self.orders[id];
            self.book.openOrders -= 1;
            return (closed, remainingIn, donatedFee, remainingFee);
        }

        uint128 newKey = priceKey(isBuy(info.zeroForOne), remainingIn, remainingMin);
        bool relocate =
            newKey != info.priceKey || (self.book.orderingMode == OrderingMode.PriorityFee && remainingFee != oldFee);
        if (relocate) _remove(self, id, info);
        info.amountIn = remainingIn;
        info.amountOutMin = remainingMin;
        info.priorityFee = uint64(remainingFee);
        info.priceKey = newKey;
        if (relocate) _append(self, id, info);
    }

    /// @dev `setOrderingMode`: only while the book is empty.
    function setOrderingMode(State storage self, OrderingMode mode) internal {
        if (self.book.openOrders != 0) revert BookNotEmpty();
        self.book.orderingMode = mode;
    }

    /* ────────────────────────────────── queries ────────────────────────────────── */

    /// @dev `bestOrder(isBuy)`: the id at the best price on that side — `bids.best(true)` / `asks.best(false)` —
    ///      then `bestAtPrice`. Returns `(0, 0)` on an empty side.
    function bestOrder(State storage self, bool buySide) internal view returns (bytes32 id, uint128 key) {
        (bool found, uint128 price) = _tree(self.book, buySide).best(buySide);
        if (!found) return (bytes32(0), 0);
        return (bestAtPrice(self, _level(self.book, buySide, price)), price);
    }

    /// @dev `bestAtPrice`: highest bid then earliest sequence in `PriorityFee` mode; the queue head in `FIFO`.
    function bestAtPrice(State storage self, PriceLevel storage lvl) internal view returns (bytes32) {
        if (self.book.orderingMode == OrderingMode.PriorityFee) {
            (bool found, uint128 key) = lvl.priorityOrders.best(true);
            return found ? lvl.priorityOrderIds[key] : bytes32(0);
        }
        return lvl.head;
    }

    function level(State storage self, bool buySide, uint128 key) internal view returns (PriceLevel storage) {
        return _level(self.book, buySide, key);
    }

    /* ─────────────────────────────────── keys ─────────────────────────────────── */

    /// @dev `_priceKey`: WAD price, `amountIn / amountOut` for bids and `amountOut / amountIn` for asks (so a
    ///      higher key is always a better price for the counterparty), clamped into `[1, 2^128 − 1]`.
    function priceKey(bool buy, uint256 amountIn, uint256 amountOut) internal pure returns (uint128) {
        uint256 raw =
            buy ? Math.mulDiv(amountIn, PRICE_SCALE, amountOut) : Math.mulDiv(amountOut, PRICE_SCALE, amountIn);
        if (raw == 0) return 1;
        if (raw > MAX_PRICE_KEY) return MAX_PRICE_KEY;
        return uint128(raw);
    }

    /// @dev `_priorityKey(fee, sequence) = (fee << 64) | (maxUint64 − sequence)`: lexicographic, higher bid
    ///      first, then earlier sequence (`Priority.lean` `priorityKey_lt_iff`).
    function priorityKey(uint64 fee, uint64 sequence) internal pure returns (uint128) {
        return (uint128(fee) << 64) | uint128(type(uint64).max - sequence);
    }

    /* ────────────────────────────── level maintenance ────────────────────────────── */

    function _tree(Book storage book, bool buySide) private view returns (RadixPriceTree.Tree storage) {
        return buySide ? book.bids : book.asks;
    }

    function _level(Book storage book, bool buySide, uint128 key) private view returns (PriceLevel storage) {
        return buySide ? book.bidLevels[key] : book.askLevels[key];
    }

    /// @dev `_append`: enter the order's level in sequence order (O(1) for a fresh sequence, which is larger
    ///      than every live one) and, in `PriorityFee` mode, index it by priority key. Creates the level in
    ///      the price tree when it was empty.
    function _append(State storage self, bytes32 id, OrderInfo storage info) private {
        Book storage book = self.book;
        bool buySide = isBuy(info.zeroForOne);
        PriceLevel storage lvl = _level(book, buySide, info.priceKey);
        if (lvl.count == 0) _tree(book, buySide).insert(info.priceKey);

        bytes32 cursor = lvl.tail;
        while (cursor != bytes32(0) && self.orders[cursor].sequence > info.sequence) {
            cursor = self.orders[cursor].previous;
        }
        if (cursor == bytes32(0)) {
            bytes32 head = lvl.head;
            info.previous = bytes32(0);
            info.next = head;
            if (head != bytes32(0)) self.orders[head].previous = id;
            else lvl.tail = id;
            lvl.head = id;
        } else {
            OrderInfo storage predecessor = self.orders[cursor];
            bytes32 next = predecessor.next;
            info.previous = cursor;
            info.next = next;
            if (next != bytes32(0)) self.orders[next].previous = id;
            else lvl.tail = id;
            predecessor.next = id;
        }
        lvl.count += 1;

        if (book.orderingMode == OrderingMode.PriorityFee) {
            uint128 pk = priorityKey(info.priorityFee, info.sequence);
            info.priorityKey = pk;
            lvl.priorityOrders.insert(pk);
            lvl.priorityOrderIds[pk] = id;
        }
    }

    /// @dev `_remove`: leave the level; drop the level from the price tree when it empties.
    function _remove(State storage self, bytes32, OrderInfo storage info) private {
        Book storage book = self.book;
        bool buySide = isBuy(info.zeroForOne);
        PriceLevel storage lvl = _level(book, buySide, info.priceKey);

        bytes32 previous = info.previous;
        bytes32 next = info.next;
        if (previous != bytes32(0)) self.orders[previous].next = next;
        else lvl.head = next;
        if (next != bytes32(0)) self.orders[next].previous = previous;
        else lvl.tail = previous;
        info.previous = bytes32(0);
        info.next = bytes32(0);
        lvl.count -= 1;

        if (book.orderingMode == OrderingMode.PriorityFee) {
            lvl.priorityOrders.remove(info.priorityKey);
            delete lvl.priorityOrderIds[info.priorityKey];
            info.priorityKey = 0;
        }
        if (lvl.count == 0) _tree(book, buySide).remove(info.priceKey);
    }
}
