// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {IHooks} from "v4-core/interfaces/IHooks.sol";
import {IPoolManager} from "v4-core/interfaces/IPoolManager.sol";
import {Hooks} from "v4-core/libraries/Hooks.sol";
import {LPFeeLibrary} from "v4-core/libraries/LPFeeLibrary.sol";
import {TickMath} from "v4-core/libraries/TickMath.sol";
import {TransientStateLibrary} from "v4-core/libraries/TransientStateLibrary.sol";
import {Currency, CurrencyLibrary} from "v4-core/types/Currency.sol";
import {PoolKey} from "v4-core/types/PoolKey.sol";
import {PoolId, PoolIdLibrary} from "v4-core/types/PoolId.sol";
import {BalanceDelta, BalanceDeltaLibrary} from "v4-core/types/BalanceDelta.sol";
import {BeforeSwapDelta, BeforeSwapDeltaLibrary, toBeforeSwapDelta} from "v4-core/types/BeforeSwapDelta.sol";
import {EIP712} from "@openzeppelin/contracts/utils/cryptography/EIP712.sol";
import {SignatureChecker} from "@openzeppelin/contracts/utils/cryptography/SignatureChecker.sol";

import {HookSettlement} from "./HookSettlement.sol";
import {Owned2Step} from "./Owned2Step.sol";
import {AsyncOrderLibrary} from "./types/AsyncOrder.sol";
import {AsyncFiller} from "./libraries/AsyncFiller.sol";
import {AsyncMatching} from "./libraries/AsyncMatching.sol";
import {CurrencySettler} from "./libraries/CurrencySettler.sol";
import {OrderSignatures} from "./libraries/OrderSignatures.sol";
import {ProtocolFee} from "./libraries/ProtocolFee.sol";

/// @title AsyncSwap
/// @notice Uniswap v4 hook that turns an exact-input swap into a resting limit order, escrowed as the hook's
///         ERC-6909 claims in the PoolManager, and matches, fills, cancels and reprices such orders.
/// @dev Spec: `AsyncSwapProtocol/V2/Model.lean` (every entry point below is a body there), `V2/Spec.lean`
///      (delta neutrality, frame), `V2/Settlement.lean` (what each party receives, backing),
///      `V2/Invariants.lean` (`Escrow`: the hook's claims equal, per currency, the open orders' remaining
///      input plus their bids), `V2/Conservation.lean`, `AsyncSwapSpec/Book.lean`, `Admin.lean`.
///
///      Authorization follows the model: whoever creates, fills or cancels on a maker's behalf must be an
///      executor the maker granted (`isExecutor[maker][executor]`); makers reprice and cancel themselves.
///      Matching and liquidity fills are permissionless inside any unlock. Native legs are paid as ERC-6909
///      claims of currency0 (see `NativeClaims`).
contract AsyncSwap is IHooks, HookSettlement, Owned2Step, EIP712 {
    using AsyncFiller for AsyncFiller.State;
    using CurrencySettler for Currency;
    using CurrencyLibrary for Currency;
    using PoolIdLibrary for PoolKey;
    using TransientStateLibrary for IPoolManager;
    using BalanceDeltaLibrary for BalanceDelta;

    /// @notice `hookData` of the creating swap.
    struct UserParams {
        address user;
        address executor;
        uint256 amountOutMin;
        uint256 priorityFee;
        bytes32 salt;
    }

    uint256 public constant MAX_MATCHES_PER_CALL = AsyncMatching.MAX_MATCHES_PER_CALL;
    /// @notice LP fee (hundredths of a bip) the pool charges on `fillFromPoolLiquidity`: 0.30%.
    uint24 public constant POOL_LIQUIDITY_FILL_FEE = 3000;

    /// @dev Transient: native output deposited by the filler for the fill in progress (`PENDING_NATIVE_DEPOSIT_SLOT`).
    bytes32 private constant PENDING_NATIVE_DEPOSIT_SLOT = keccak256("AsyncSwap.pendingNativeDeposit");
    /// @dev Transient: the id assigned by the most recent `beforeSwap`, read back by the creating router.
    bytes32 private constant LAST_ORDER_ID_SLOT = keccak256("AsyncSwap.lastOrderId");

    mapping(PoolId => AsyncFiller.State) internal asyncOrders;
    /// @notice Unordered nonces for signed `setExecutor` / `updatePrice` (`Admin.lean`).
    mapping(address => mapping(uint256 => bool)) public nonceUsed;

    error NotPoolManager();
    error NotUnlocked();
    error HookNotImplemented();
    error ExactInputRequired();
    error AmountTooLarge(uint256 amountIn);
    error ExecutorMismatch(address expected, address actual);
    error UnauthorizedExecutor(address maker, address executor);
    error NotOwnerOrExecutor(bytes32 id);
    error InsufficientNativeDeposit(uint256 required, uint256 available);
    error SignatureExpired(uint256 deadline);
    error NonceAlreadyUsed(address signer, uint256 nonce);
    error InvalidSignature();
    error InvalidMaxMatches(uint256 maxMatches);
    error NoActiveLiquidity();
    error PartialLiquidityFill(uint256 amountIn, uint256 swapped);
    error LimitPriceNotMet(uint256 amountOutMin, uint256 amountOut);
    error NativeTransferFailed();
    error NumeraireRequired();
    error DynamicFeeRequired();

    event OrderCreated(
        PoolId indexed poolId,
        bytes32 indexed id,
        address indexed owner,
        bool zeroForOne,
        uint256 amountIn,
        uint256 amountOutMin,
        uint256 priorityFee,
        bytes32 salt,
        uint64 sequence
    );
    event OrderFilled(
        PoolId indexed poolId,
        bytes32 indexed id,
        address indexed filler,
        uint256 amountIn,
        uint256 amountOut,
        uint256 fee
    );
    event OrderCancelled(PoolId indexed poolId, bytes32 indexed id, uint256 refund);
    event OrdersMatched(
        PoolId indexed poolId, bytes32 indexed sellId, bytes32 indexed buyId, uint256 asset, uint256 quote
    );
    event OrderReduced(
        PoolId indexed poolId, bytes32 indexed id, uint256 amountIn, uint256 amountOutMin, uint64 priorityFee
    );
    event OrderClosed(PoolId indexed poolId, bytes32 indexed id, uint256 refund);
    event OrderRepriced(PoolId indexed poolId, bytes32 indexed id, uint256 newAmountOutMin, uint64 sequence);
    event LiquidityFilled(PoolId indexed poolId, bytes32 indexed id, uint256 amountIn, uint256 amountOut);
    event ExecutorSet(PoolId indexed poolId, address indexed maker, address indexed executor, bool allow);
    event NonceInvalidated(address indexed signer, uint256 nonce);
    event OrderingModeSet(PoolId indexed poolId, AsyncFiller.OrderingMode mode);
    event Swept(Currency indexed currency, address indexed to, uint256 amount);

    constructor(IPoolManager _manager, address _feeVault, Currency _numeraire, address _owner)
        HookSettlement(_manager, _feeVault, _numeraire)
        Owned2Step(_owner)
        EIP712("AsyncSwap", "2")
    {
        Hooks.validateHookPermissions(this, getHookPermissions());
    }

    /// @dev `receive()` feeds the transient native ledger a filler's deposit is forwarded into.
    receive() external payable {
        _tstore(PENDING_NATIVE_DEPOSIT_SLOT, bytes32(uint256(_tload(PENDING_NATIVE_DEPOSIT_SLOT)) + msg.value));
    }

    modifier onlyManager() {
        if (msg.sender != address(manager)) revert NotPoolManager();
        _;
    }

    modifier whenUnlocked() {
        if (!manager.isUnlocked()) revert NotUnlocked();
        _;
    }

    function getHookPermissions() public pure returns (Hooks.Permissions memory) {
        return Hooks.Permissions({
            beforeInitialize: true,
            afterInitialize: false,
            beforeAddLiquidity: false,
            afterAddLiquidity: false,
            beforeRemoveLiquidity: false,
            afterRemoveLiquidity: false,
            beforeSwap: true,
            afterSwap: false,
            beforeDonate: false,
            afterDonate: false,
            beforeSwapReturnDelta: true,
            afterSwapReturnDelta: false,
            afterAddLiquidityReturnDelta: false,
            afterRemoveLiquidityReturnDelta: false
        });
    }

    /// @notice Only pools that contain the numeraire can use the hook: the book's sides, its prices and the
    ///         bids are all denominated in it. The fee must be the dynamic-fee flag, so a pair cannot be split
    ///         across several fee tiers (each a separate book); the hook sets the LP fee itself.
    function beforeInitialize(address, PoolKey calldata key, uint160) external view onlyManager returns (bytes4) {
        if (!(key.currency0 == numeraire || key.currency1 == numeraire)) revert NumeraireRequired();
        if (key.fee != LPFeeLibrary.DYNAMIC_FEE_FLAG) revert DynamicFeeRequired();
        return IHooks.beforeInitialize.selector;
    }

    /* ───────────────────────────── create (`beforeSwap`) ───────────────────────────── */

    /// @dev `_beforeSwap` + `_createOrder` + `addOrder` (`createBody`): the whole exact input becomes the
    ///      hook's claim and the order is opened; a non-zero bid is escrowed in the same call
    ///      (`priorityFeeBody`), so `created_order_escrowed` holds for every stored order. The caller of
    ///      `PoolManager.swap` must be the maker's executor named in `hookData`.
    function beforeSwap(
        address sender,
        PoolKey calldata key,
        IPoolManager.SwapParams calldata params,
        bytes calldata hookData
    ) external onlyManager returns (bytes4, BeforeSwapDelta, uint24) {
        // `fillFromPoolLiquidity` swaps the escrow through the pool: let the pool execute it.
        if (sender == address(this)) return (IHooks.beforeSwap.selector, BeforeSwapDeltaLibrary.ZERO_DELTA, 0);

        if (params.amountSpecified >= 0) revert ExactInputRequired();
        uint256 amountIn = uint256(-params.amountSpecified);
        if (amountIn > uint128(type(int128).max)) revert AmountTooLarge(amountIn);

        _open(sender, key, params.zeroForOne, amountIn, abi.decode(hookData, (UserParams)));

        return (IHooks.beforeSwap.selector, toBeforeSwapDelta(int128(uint128(amountIn)), 0), 0);
    }

    function _open(address sender, PoolKey calldata key, bool zeroForOne, uint256 amountIn, UserParams memory up)
        private
    {
        if (sender != up.executor) revert ExecutorMismatch(up.executor, sender);
        AsyncFiller.State storage state = asyncOrders[key.toId()];
        if (!state.isExecutor[up.user][sender]) revert UnauthorizedExecutor(up.user, sender);

        bytes32 id = _createOrder(state, key, zeroForOne, amountIn, up);

        (zeroForOne ? key.currency0 : key.currency1).take(manager, address(this), amountIn, true);
        if (up.priorityFee != 0) numeraire.take(manager, address(this), up.priorityFee, true);
        _tstore(LAST_ORDER_ID_SLOT, id);
    }

    function _createOrder(
        AsyncFiller.State storage state,
        PoolKey calldata key,
        bool zeroForOne,
        uint256 amountIn,
        UserParams memory up
    ) private returns (bytes32 id) {
        PoolId poolId = key.toId();
        bytes32 salt = up.salt;
        id = AsyncOrderLibrary.orderId(poolId, up.user, zeroForOne, salt);
        // Salt collision walk: the chosen slot is free.
        while (state.orders[id].amountIn != 0) {
            salt = keccak256(abi.encode(salt));
            id = AsyncOrderLibrary.orderId(poolId, up.user, zeroForOne, salt);
        }
        bool buy = (zeroForOne ? key.currency0 : key.currency1) == numeraire;
        uint64 sequence = state.addOrder(id, up.user, zeroForOne, buy, amountIn, up.amountOutMin, up.priorityFee);
        emit OrderCreated(poolId, id, up.user, zeroForOne, amountIn, up.amountOutMin, up.priorityFee, salt, sequence);
    }

    /* ─────────────────────────────────── matching ─────────────────────────────────── */

    /// @notice `matchNewOrder`: match `id` against the best resting orders on the other side while the book
    ///         is crossed, at most `maxMatches ≤ 8` times.
    function matchNewOrder(PoolKey calldata key, bytes32 id, uint256 maxMatches)
        external
        whenUnlocked
        returns (uint256 matches)
    {
        if (maxMatches > MAX_MATCHES_PER_CALL) revert InvalidMaxMatches(maxMatches);
        return _matchIncoming(key, asyncOrders[key.toId()], id, maxMatches);
    }

    /// @notice `matchBook`: anyone continues a crossed book.
    function matchBook(PoolKey calldata key, uint256 maxMatches) external whenUnlocked returns (uint256 matches) {
        if (maxMatches == 0 || maxMatches > MAX_MATCHES_PER_CALL) revert InvalidMaxMatches(maxMatches);
        return _matchBook(key, asyncOrders[key.toId()], maxMatches);
    }

    /// @dev `matchIncoming`: the crossed check is `ask key ≤ bid key` on the stored keys (`matchGuard`).
    function _matchIncoming(PoolKey calldata key, AsyncFiller.State storage state, bytes32 id, uint256 maxMatches)
        private
        returns (uint256 matches)
    {
        while (matches < maxMatches) {
            AsyncFiller.OrderInfo storage info = state.orders[id];
            if (info.amountIn == 0) break;
            bool incomingBuy = info.buy;
            (bytes32 restingId, uint128 restingKey) = state.bestOrder(!incomingBuy);
            if (restingId == bytes32(0)) break;
            if (incomingBuy ? info.priceKey < restingKey : restingKey < info.priceKey) break;
            bool matched = incomingBuy ? _matchPair(key, state, restingId, id) : _matchPair(key, state, id, restingId);
            if (!matched) break;
            unchecked {
                ++matches;
            }
        }
    }

    function _matchBook(PoolKey calldata key, AsyncFiller.State storage state, uint256 maxMatches)
        private
        returns (uint256 matches)
    {
        while (matches < maxMatches) {
            (bytes32 bidId, uint128 bidKey) = state.bestOrder(true);
            if (bidId == bytes32(0)) break;
            (bytes32 askId, uint128 askKey) = state.bestOrder(false);
            if (askId == bytes32(0)) break;
            if (bidKey < askKey) break;
            if (!_matchPair(key, state, askId, bidId)) break;
            unchecked {
                ++matches;
            }
        }
    }

    /// @dev `_matchPair`: the older order rests and its price sizes the trade (`_matchAmounts`); a zero result
    ///      (rounding) is reported as "no match" and never executed. Then both sides are reduced.
    function _matchPair(PoolKey calldata key, AsyncFiller.State storage state, bytes32 sellId, bytes32 buyId)
        private
        returns (bool)
    {
        AsyncFiller.OrderInfo storage sell = state.orders[sellId];
        AsyncFiller.OrderInfo storage buy = state.orders[buyId];
        bool restingBuy = buy.sequence < sell.sequence;
        (uint256 asset, uint256 quote) =
            AsyncMatching.matchAmounts(sell.amountIn, sell.amountOutMin, buy.amountIn, buy.amountOutMin, restingBuy);
        if (asset == 0 || quote == 0) return false;
        address sellOwner = sell.owner;
        address buyOwner = buy.owner;
        _reduceAfterMatch(key, state, sellId, buyOwner, asset, quote);
        _reduceAfterMatch(key, state, buyId, sellOwner, quote, asset);
        emit OrdersMatched(key.toId(), sellId, buyId, asset, quote);
        return true;
    }

    /// @dev `_transferEscrow` + `_settleMatchedPriorityFee` + `_reduceAfterMatch` for one side
    ///      (`reduceSideBody`): the consumed input goes to the counterparty, the pro-rata bid is donated, and
    ///      the order either stays open with reduced amounts or closes — settling the rest of its bid and
    ///      refunding its unused input.
    function _reduceAfterMatch(
        PoolKey calldata key,
        AsyncFiller.State storage state,
        bytes32 id,
        address counterparty,
        uint256 used,
        uint256 received
    ) private {
        AsyncFiller.OrderInfo storage info = state.orders[id];
        address owner = info.owner;
        Currency input = info.zeroForOne ? key.currency0 : key.currency1;
        (bool closed, uint256 remainingIn, uint256 donatedFee, uint256 remainingFee) = state.reduce(id, used, received);
        _transferEscrow(input, counterparty, used);
        _settlePriorityFee(key, donatedFee);
        if (closed) {
            _settlePriorityFee(key, remainingFee);
            _transferEscrow(input, owner, remainingIn);
            emit OrderClosed(key.toId(), id, remainingIn);
        } else {
            emit OrderReduced(key.toId(), id, remainingIn, info.amountOutMin, uint64(remainingFee));
        }
    }

    /* ────────────────────────────────── fill / cancel ────────────────────────────────── */

    /// @notice `executeOrder` (`fillBody`): an executor fills the order in full. The executor has already
    ///         delivered the live gross output — `amountOutMin + calculatePoolFee(amountOutMin)` — either as
    ///         native value forwarded to this contract or as a `settleFor(hook)` credit. The maker receives
    ///         exactly the stored minimum, the vault the fee, the filler the whole escrow; the bid is settled.
    function executeOrder(PoolKey calldata key, bytes32 id, address filler)
        external
        whenUnlocked
        returns (uint256 amountIn, uint256 amountOut, uint256 fee)
    {
        AsyncFiller.State storage state = asyncOrders[key.toId()];
        AsyncFiller.OrderInfo storage info = state.orders[id];
        if (info.amountIn == 0) revert AsyncFiller.OrderNotFound(id);
        if (!state.isExecutor[info.owner][msg.sender]) revert UnauthorizedExecutor(info.owner, msg.sender);
        AsyncFiller.OrderInfo memory o = state.close(id);

        (Currency input, Currency output) =
            o.zeroForOne ? (key.currency0, key.currency1) : (key.currency1, key.currency0);
        fee = calculatePoolFee(key.fee, o.amountOutMin);
        uint256 live = o.amountOutMin + fee;

        if (output.isAddressZero()) {
            uint256 pending = uint256(_tload(PENDING_NATIVE_DEPOSIT_SLOT));
            if (pending < live) revert InsufficientNativeDeposit(live, pending);
            _tstore(PENDING_NATIVE_DEPOSIT_SLOT, bytes32(pending - live));
            output.settle(manager, address(this), live, false);
        }
        output.take(manager, o.owner, o.amountOutMin, output.isAddressZero());
        if (fee != 0) output.take(manager, feeVault, fee, true);
        _transferEscrow(input, filler, o.amountIn);
        _settlePriorityFee(key, o.priorityFee);
        _tstore(PENDING_NATIVE_DEPOSIT_SLOT, bytes32(0));

        emit OrderFilled(key.toId(), id, filler, o.amountIn, o.amountOutMin, fee);
        return (o.amountIn, o.amountOutMin, fee);
    }

    /// @notice `cancelOrder` (`cancelBody`): the maker, or an executor the maker granted, closes the order.
    ///         The remaining escrow is refunded to the maker; the bid is not.
    function cancelOrder(PoolKey calldata key, bytes32 id) external whenUnlocked returns (uint256 refund) {
        AsyncFiller.State storage state = asyncOrders[key.toId()];
        AsyncFiller.OrderInfo storage info = state.orders[id];
        if (info.amountIn == 0) revert AsyncFiller.OrderNotFound(id);
        if (msg.sender != info.owner && !state.isExecutor[info.owner][msg.sender]) revert NotOwnerOrExecutor(id);
        AsyncFiller.OrderInfo memory o = state.close(id);
        _transferEscrow(o.zeroForOne ? key.currency0 : key.currency1, o.owner, o.amountIn);
        _settlePriorityFee(key, o.priorityFee);
        emit OrderCancelled(key.toId(), id, o.amountIn);
        return o.amountIn;
    }

    /// @notice `fillFromPoolLiquidity` (`liquidityFillBody`): anyone swaps the whole escrow through the pool;
    ///         the maker is paid the pool's output, which must reach their minimum.
    function fillFromPoolLiquidity(PoolKey calldata key, bytes32 id) external whenUnlocked returns (uint256 amountOut) {
        AsyncFiller.State storage state = asyncOrders[key.toId()];
        if (state.orders[id].amountIn == 0) revert AsyncFiller.OrderNotFound(id);
        if (!_hasLiquidity(key)) revert NoActiveLiquidity();
        AsyncFiller.OrderInfo memory o = state.close(id);

        (Currency input, Currency output) =
            o.zeroForOne ? (key.currency0, key.currency1) : (key.currency1, key.currency0);
        input.settle(manager, address(this), o.amountIn, true);
        // A dynamic-fee pool starts at 0, and this is the only swap that reaches the pool's liquidity.
        manager.updateDynamicLPFee(key, POOL_LIQUIDITY_FILL_FEE);
        BalanceDelta delta = manager.swap(
            key,
            IPoolManager.SwapParams({
                zeroForOne: o.zeroForOne,
                amountSpecified: -int256(o.amountIn),
                sqrtPriceLimitX96: o.zeroForOne ? TickMath.MIN_SQRT_PRICE + 1 : TickMath.MAX_SQRT_PRICE - 1
            }),
            ""
        );
        (int128 deltaIn, int128 deltaOut) =
            o.zeroForOne ? (delta.amount0(), delta.amount1()) : (delta.amount1(), delta.amount0());
        if (deltaIn != -int128(uint128(o.amountIn))) {
            revert PartialLiquidityFill(o.amountIn, uint256(uint128(-deltaIn)));
        }
        amountOut = uint256(uint128(deltaOut));
        if (amountOut < o.amountOutMin) revert LimitPriceNotMet(o.amountOutMin, amountOut);

        output.take(manager, o.owner, amountOut, output.isAddressZero());
        _settlePriorityFee(key, o.priorityFee);
        emit LiquidityFilled(key.toId(), id, o.amountIn, amountOut);
    }

    /* ─────────────────────────────── maker actions ─────────────────────────────── */

    /// @notice `updatePrice`: maker-only; no claims move; the order re-enters its level last.
    function updatePrice(PoolKey calldata key, bytes32 id, uint256 newAmountOutMin) external {
        uint64 sequence = asyncOrders[key.toId()].updatePrice(id, msg.sender, newAmountOutMin);
        emit OrderRepriced(key.toId(), id, newAmountOutMin, sequence);
    }

    /// @notice `updatePriceWithSig`: the maker signs `UpdatePrice(maker, tokenIn, tokenOut, amountIn(stored),
    ///         newAmountOutMin, orderId, nonce, deadline)` in this contract's domain.
    function updatePriceWithSig(
        PoolKey calldata key,
        bytes32 id,
        uint256 newAmountOutMin,
        uint256 nonce,
        uint256 deadline,
        bytes calldata signature
    ) external {
        AsyncFiller.State storage state = asyncOrders[key.toId()];
        AsyncFiller.OrderInfo storage info = state.orders[id];
        if (info.amountIn == 0) revert AsyncFiller.OrderNotFound(id);
        address maker = info.owner;
        bytes32 digest = _hashTypedDataV4(
            OrderSignatures.hashUpdatePrice(
                key, maker, info.zeroForOne, info.amountIn, newAmountOutMin, id, nonce, deadline
            )
        );
        _verify(maker, nonce, deadline, digest, signature);
        uint64 sequence = state.updatePrice(id, maker, newAmountOutMin);
        emit OrderRepriced(key.toId(), id, newAmountOutMin, sequence);
    }

    /// @notice Grant or revoke an executor for the caller's orders in `key`.
    function setExecutor(PoolKey calldata key, address executor, bool allow) external {
        asyncOrders[key.toId()].isExecutor[msg.sender][executor] = allow;
        emit ExecutorSet(key.toId(), msg.sender, executor, allow);
    }

    /// @notice `setExecutorWithSig`: `SetExecutor(maker, executor, allow, pool, nonce, deadline)` signed by the maker.
    function setExecutorWithSig(
        PoolKey calldata key,
        address maker,
        address executor,
        bool allow,
        uint256 nonce,
        uint256 deadline,
        bytes calldata signature
    ) external {
        bytes32 digest = _hashTypedDataV4(OrderSignatures.hashSetExecutor(key, maker, executor, allow, nonce, deadline));
        _verify(maker, nonce, deadline, digest, signature);
        asyncOrders[key.toId()].isExecutor[maker][executor] = allow;
        emit ExecutorSet(key.toId(), maker, executor, allow);
    }

    /// @notice Burn one of the caller's nonces so a signature carrying it can never be used.
    function invalidateNonce(uint256 nonce) external {
        if (nonceUsed[msg.sender][nonce]) revert NonceAlreadyUsed(msg.sender, nonce);
        nonceUsed[msg.sender][nonce] = true;
        emit NonceInvalidated(msg.sender, nonce);
    }

    /// @dev `_verify`: reject past `deadline`, burn the nonce, then check the signature (EOA or ERC-1271).
    function _verify(address signer, uint256 nonce, uint256 deadline, bytes32 digest, bytes calldata signature)
        private
    {
        if (block.timestamp > deadline) revert SignatureExpired(deadline);
        if (nonceUsed[signer][nonce]) revert NonceAlreadyUsed(signer, nonce);
        nonceUsed[signer][nonce] = true;
        if (!SignatureChecker.isValidSignatureNow(signer, digest, signature)) revert InvalidSignature();
    }

    /* ───────────────────────────────────── admin ───────────────────────────────────── */

    /// @notice `setOrderingMode`: only while the pool's book is empty.
    function setOrderingMode(PoolKey calldata key, AsyncFiller.OrderingMode mode) external onlyOwner {
        asyncOrders[key.toId()].setOrderingMode(mode);
        emit OrderingModeSet(key.toId(), mode);
    }

    /// @notice `sweep`: move this contract's *own* token balance (never claims, so never escrow) to `to`.
    function sweep(Currency currency, address to) external onlyOwner returns (uint256 amount) {
        if (to == address(0)) revert ZeroAddress();
        amount = currency.balanceOfSelf();
        if (amount != 0) currency.transfer(to, amount);
        emit Swept(currency, to, amount);
    }

    /// @notice `calculatePoolFee`: 30 bps of gross, rounded down, expressed on the maker's net minimum.
    function calculatePoolFee(uint24, uint256 amount) public pure virtual returns (uint256) {
        return ProtocolFee.poolFee(amount);
    }

    /* ───────────────────────────────────── views ───────────────────────────────────── */

    function getOrder(PoolKey calldata key, bytes32 id) external view returns (AsyncFiller.OrderInfo memory) {
        return asyncOrders[key.toId()].orders[id];
    }

    function isExecutor(PoolKey calldata key, address maker, address executor) external view returns (bool) {
        return asyncOrders[key.toId()].isExecutor[maker][executor];
    }

    /// @notice The best order on a side: `(id, priceKey)`, `(0, 0)` when the side is empty.
    function bestOrder(PoolKey calldata key, bool buySide) external view returns (bytes32 id, uint128 priceKey) {
        return asyncOrders[key.toId()].bestOrder(buySide);
    }

    function orderingMode(PoolKey calldata key) external view returns (AsyncFiller.OrderingMode) {
        return asyncOrders[key.toId()].book.orderingMode;
    }

    function openOrders(PoolKey calldata key) external view returns (uint256) {
        return asyncOrders[key.toId()].book.openOrders;
    }

    function nextSequence(PoolKey calldata key) external view returns (uint64) {
        return asyncOrders[key.toId()].book.nextSequence;
    }

    /// @notice The id assigned by the most recent `beforeSwap` in this transaction.
    function lastOrderId() external view returns (bytes32) {
        return _tload(LAST_ORDER_ID_SLOT);
    }

    function pendingNativeDeposit() external view returns (uint256) {
        return uint256(_tload(PENDING_NATIVE_DEPOSIT_SLOT));
    }

    function DOMAIN_SEPARATOR() external view returns (bytes32) {
        return _domainSeparatorV4();
    }

    /* ─────────────────────────────── unused hook entries ─────────────────────────────── */

    function afterInitialize(address, PoolKey calldata, uint160, int24) external pure returns (bytes4) {
        revert HookNotImplemented();
    }

    function beforeAddLiquidity(address, PoolKey calldata, IPoolManager.ModifyLiquidityParams calldata, bytes calldata)
        external
        pure
        returns (bytes4)
    {
        revert HookNotImplemented();
    }

    function afterAddLiquidity(
        address,
        PoolKey calldata,
        IPoolManager.ModifyLiquidityParams calldata,
        BalanceDelta,
        BalanceDelta,
        bytes calldata
    ) external pure returns (bytes4, BalanceDelta) {
        revert HookNotImplemented();
    }

    function beforeRemoveLiquidity(
        address,
        PoolKey calldata,
        IPoolManager.ModifyLiquidityParams calldata,
        bytes calldata
    ) external pure returns (bytes4) {
        revert HookNotImplemented();
    }

    function afterRemoveLiquidity(
        address,
        PoolKey calldata,
        IPoolManager.ModifyLiquidityParams calldata,
        BalanceDelta,
        BalanceDelta,
        bytes calldata
    ) external pure returns (bytes4, BalanceDelta) {
        revert HookNotImplemented();
    }

    function afterSwap(address, PoolKey calldata, IPoolManager.SwapParams calldata, BalanceDelta, bytes calldata)
        external
        pure
        returns (bytes4, int128)
    {
        revert HookNotImplemented();
    }

    function beforeDonate(address, PoolKey calldata, uint256, uint256, bytes calldata) external pure returns (bytes4) {
        revert HookNotImplemented();
    }

    function afterDonate(address, PoolKey calldata, uint256, uint256, bytes calldata) external pure returns (bytes4) {
        revert HookNotImplemented();
    }

    /* ─────────────────────────────────── transient ─────────────────────────────────── */

    function _tload(bytes32 slot) private view returns (bytes32 value) {
        assembly ("memory-safe") {
            value := tload(slot)
        }
    }

    function _tstore(bytes32 slot, bytes32 value) private {
        assembly ("memory-safe") {
            tstore(slot, value)
        }
    }
}
