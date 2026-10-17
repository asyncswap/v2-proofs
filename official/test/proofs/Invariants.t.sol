// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {Test, Vm} from "forge-std/Test.sol";
import {Currency, CurrencyLibrary} from "v4-core/types/Currency.sol";
import {PoolId} from "v4-core/types/PoolId.sol";
import {PoolIdLibrary, PoolKey} from "v4-core/types/PoolKey.sol";
import {AsyncSwap} from "@async-swap/AsyncSwap.sol";
import {Router} from "@async-swap/Router.sol";
import {FeeVault} from "@async-swap/FeeVault.sol";
import {AsyncOrder} from "@async-swap/types/AsyncOrder.sol";
import {AsyncFiller} from "@async-swap/libraries/AsyncFiller.sol";
import {OrderSignatures} from "@async-swap/libraries/OrderSignatures.sol";
import {Permit2Bytecode} from "../utils/Permit2Bytecode.sol";
import {ProofBase, IPermit2Domain} from "./ProofBase.sol";

/// @notice Drives one pool through every entry point — `Router.swap` (maker salt and derived salt),
///         `Router.swapWithSig`, `Router.fillOrder`, `Router.cancelOrder`, `Router.cancelWithSig`,
///         `AsyncSwap.updatePrice`, `AsyncSwap.updatePriceWithSig`, `Router.matchBook`,
///         `Router.fillFromPoolLiquidity`, `AsyncSwap.setExecutor(WithSig)`, `FeeVault.collect` — remembering
///         every order it placed (with the final salt, read from `AsyncOrderCreated`).
contract ProofHandler is Test {
    using PoolIdLibrary for PoolKey;

    AsyncSwap immutable hook;
    Router immutable router;
    address immutable protocolOwner;
    PoolKey key;
    bool immutable priorityMode;
    address[] actors;
    uint256[] pks;

    AsyncOrder[] public placed;
    uint256 public calls;
    uint256 public created;
    uint256 nonceCounter = 1_000;

    mapping(bytes4 => uint256) public hits;
    /// @dev Successful calls per entry point, so a run can be checked for coverage.
    mapping(bytes4 => uint256) public oks;

    constructor(
        AsyncSwap _hook,
        Router _router,
        address _protocolOwner,
        PoolKey memory _key,
        bool _priorityMode,
        address[] memory _actors,
        uint256[] memory _pks
    ) {
        hook = _hook;
        router = _router;
        protocolOwner = _protocolOwner;
        key = _key;
        priorityMode = _priorityMode;
        actors = _actors;
        pks = _pks;
    }

    function placedCount() external view returns (uint256) {
        return placed.length;
    }

    function placedAt(uint256 i) external view returns (AsyncOrder memory) {
        return placed[i];
    }

    function actorCount() external view returns (uint256) {
        return actors.length;
    }

    function actorAt(uint256 i) external view returns (address) {
        return actors[i];
    }

    /* ─────────────────────────────── create ─────────────────────────────── */

    function _newOrder(uint256 who, bool zeroForOne, uint256 amountIn, uint256 amountOutMin, uint256 fee)
        internal
        view
        returns (AsyncOrder memory o, uint256 actor)
    {
        actor = who % actors.length;
        // log-uniform size over [1e6, 1e21] so both the shallow pool (fallback fills) and the book see orders
        amountIn = 10 ** (6 + amountIn % 15) * (1 + (amountIn >> 8) % 9);
        // limit price on a small grid near 1 so orders share levels (FIFO queues, bid ties), cross each other
        // and the 1:1 pool; 1 in 8 fully independent
        amountOutMin = amountOutMin % 8 == 0 ? bound(amountOutMin >> 3, 1e6, 1e21) : _onGrid(amountIn, amountOutMin >> 3);
        fee = priorityMode ? bound(fee, AsyncFiller.MIN_PRIORITY_FEE, 1e9) : 0;
        o = AsyncOrder(key, actors[actor], zeroForOne, amountIn, amountOutMin, fee, 2 ** 96, bytes32(0));
    }

    uint256 public matchedLegs;
    uint256 public poolFills;

    function _tally(Vm.Log[] memory logs) internal {
        for (uint256 i; i < logs.length; ++i) {
            if (logs[i].emitter != address(hook)) continue;
            if (logs[i].topics[0] == AsyncSwap.AsyncOrdersMatched.selector) ++matchedLegs;
            if (logs[i].topics[0] == AsyncSwap.AsyncOrderLiquidityFilled.selector) ++poolFills;
        }
    }

    function _onGrid(uint256 amountIn, uint256 seed) internal pure returns (uint256) {
        uint64[8] memory ratios = [5e17, 8e17, 9e17, 1e18, 1e18, 1.1e18, 1.25e18, 2e18];
        uint256 out = amountIn * ratios[seed % 8] / 1e18;
        return out == 0 ? 1 : out;
    }

    /// @dev A new minimum for a reprice: on the grid relative to the live input half the time.
    function _newMin(AsyncOrder memory o, uint256 seed) internal view returns (uint256) {
        (uint256 amountIn,) = hook.asyncOrderInfo(key.toId(), _id(o));
        if (seed % 2 == 0 && amountIn != 0) return _onGrid(amountIn, seed >> 1);
        return bound(seed >> 1, 1e6, 1e21);
    }

    function _record(AsyncOrder memory o, Vm.Log[] memory logs) internal {
        _tally(logs);
        for (uint256 i; i < logs.length; ++i) {
            if (logs[i].emitter == address(hook) && logs[i].topics[0] == AsyncFiller.AsyncOrderCreated.selector) {
                (,,, bytes32 salt) = abi.decode(logs[i].data, (bool, uint256, uint256, bytes32));
                o.salt = salt;
                placed.push(o);
                ++created;
                return;
            }
        }
    }

    function place(
        uint256 who,
        bool zeroForOne,
        uint256 amountIn,
        uint256 amountOutMin,
        uint256 fee,
        bytes32 salt,
        bool makerSalt
    ) external {
        calls++;
        hits[this.place.selector]++;
        (AsyncOrder memory o,) = _newOrder(who, zeroForOne, amountIn, amountOutMin, fee);
        // a maker-chosen salt (official improvement) or zero for v2's derived salt; small salt space so
        // collisions exercise the walk
        o.salt = makerSalt ? bytes32(uint256(salt) % 4 + 1) : bytes32(0);
        bytes memory data =
            abi.encode(AsyncSwap.UserParams(o.owner, address(router), o.amountOutMin, o.priorityFee));
        vm.recordLogs();
        vm.prank(o.owner);
        try router.swap(o, data) {
            oks[this.place.selector]++;
            _record(o, vm.getRecordedLogs());
        } catch {
            vm.getRecordedLogs();
        }
    }

    function placeWithSig(uint256 who, bool zeroForOne, uint256 amountIn, uint256 amountOutMin, uint256 fee)
        external
    {
        calls++;
        hits[this.placeWithSig.selector]++;
        (AsyncOrder memory o, uint256 actor) = _newOrder(who, zeroForOne, amountIn, amountOutMin, fee);
        uint256 nonce = ++nonceCounter;
        uint256 deadline = block.timestamp + 1 hours;
        Router.PermitData memory permit = Router.PermitData(nonce, deadline, _permitSig(pks[actor], o, nonce, deadline));
        vm.recordLogs();
        try router.swapWithSig(o, permit, Router.ExecutorGrant(0, 0, "")) {
            oks[this.placeWithSig.selector]++;
            _record(o, vm.getRecordedLogs());
        } catch {
            vm.getRecordedLogs();
        }
    }

    function _permitSig(uint256 pk, AsyncOrder memory o, uint256 nonce, uint256 deadline)
        internal
        view
        returns (bytes memory)
    {
        bytes32 typeHash = keccak256(
            abi.encodePacked(
                "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,",
                OrderSignatures.PERMIT2_WITNESS_TYPE
            )
        );
        Currency input = o.zeroForOne ? o.key.currency0 : o.key.currency1;
        bytes32 tokenPermissions = keccak256(
            abi.encode(keccak256("TokenPermissions(address token,uint256 amount)"), Currency.unwrap(input), o.amountIn)
        );
        bytes32 structHash = keccak256(
            abi.encode(typeHash, tokenPermissions, address(router), nonce, deadline, OrderSignatures.hashOrder(o))
        );
        return _sign(
            pk,
            keccak256(abi.encodePacked("\x19\x01", IPermit2Domain(Permit2Bytecode.PERMIT2).DOMAIN_SEPARATOR(), structHash))
        );
    }

    function _sign(uint256 pk, bytes32 digest) internal pure returns (bytes memory) {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(pk, digest);
        return abi.encodePacked(r, s, v);
    }

    /* ─────────────────────────────── act on orders ─────────────────────────────── */

    function _pick(uint256 idx) internal view returns (bool ok, AsyncOrder memory o) {
        if (placed.length == 0) return (false, o);
        return (true, placed[idx % placed.length]);
    }

    function _id(AsyncOrder memory o) internal view returns (bytes32) {
        return keccak256(abi.encode(block.chainid, key.toId(), o.owner, o.zeroForOne, o.salt));
    }

    function _actorIndex(address a) internal view returns (uint256) {
        for (uint256 i; i < actors.length; ++i) {
            if (actors[i] == a) return i;
        }
        revert("unknown actor");
    }

    function fill(uint256 idx, uint256 who) external {
        calls++;
        hits[this.fill.selector]++;
        (bool ok, AsyncOrder memory o) = _pick(idx);
        if (!ok) return;
        address f = actors[who % actors.length];
        vm.prank(f);
        try router.fillOrder(o, type(uint256).max, "") {
            oks[this.fill.selector]++;
        } catch {}
    }

    function cancel(uint256 idx) external {
        calls++;
        hits[this.cancel.selector]++;
        (bool ok, AsyncOrder memory o) = _pick(idx);
        if (!ok) return;
        vm.prank(o.owner);
        try router.cancelOrder(o) {
            oks[this.cancel.selector]++;
        } catch {}
    }

    function cancelWithSig(uint256 idx) external {
        calls++;
        hits[this.cancelWithSig.selector]++;
        (bool ok, AsyncOrder memory o) = _pick(idx);
        if (!ok) return;
        bytes32 id = _id(o);
        (uint256 amountIn,) = hook.asyncOrderInfo(key.toId(), id);
        uint256 nonce = ++nonceCounter;
        uint256 deadline = block.timestamp + 1 hours;
        bytes32 structHash = OrderSignatures.hashCancel(o, id, amountIn, nonce, deadline);
        bytes memory sig = _sign(
            pks[_actorIndex(o.owner)], keccak256(abi.encodePacked("\x19\x01", router.DOMAIN_SEPARATOR(), structHash))
        );
        try router.cancelWithSig(o, nonce, deadline, sig) {
            oks[this.cancelWithSig.selector]++;
        } catch {}
    }

    function reprice(uint256 idx, uint256 newMin) external {
        calls++;
        hits[this.reprice.selector]++;
        (bool ok, AsyncOrder memory o) = _pick(idx);
        if (!ok) return;
        newMin = _newMin(o, newMin);
        vm.prank(o.owner);
        try hook.updatePrice(o, newMin) {
            oks[this.reprice.selector]++;
        } catch {}
    }

    function repriceWithSig(uint256 idx, uint256 newMin) external {
        calls++;
        hits[this.repriceWithSig.selector]++;
        (bool ok, AsyncOrder memory o) = _pick(idx);
        if (!ok) return;
        newMin = _newMin(o, newMin);
        bytes32 id = _id(o);
        (uint256 amountIn,) = hook.asyncOrderInfo(key.toId(), id);
        uint256 nonce = ++nonceCounter;
        uint256 deadline = block.timestamp + 1 hours;
        bytes32 structHash = OrderSignatures.hashUpdatePrice(o, id, amountIn, newMin, nonce, deadline);
        bytes memory sig = _sign(
            pks[_actorIndex(o.owner)], keccak256(abi.encodePacked("\x19\x01", hook.DOMAIN_SEPARATOR(), structHash))
        );
        try hook.updatePriceWithSig(o, newMin, nonce, deadline, sig) {
            oks[this.repriceWithSig.selector]++;
        } catch {}
    }

    function matchBook(uint256 n) external {
        calls++;
        hits[this.matchBook.selector]++;
        vm.recordLogs();
        try router.matchBook(key, uint8(bound(n, 1, 8))) {} catch {}
        _tally(vm.getRecordedLogs());
    }

    function liquidityFill(uint256 idx) external {
        calls++;
        hits[this.liquidityFill.selector]++;
        (bool ok, AsyncOrder memory o) = _pick(idx);
        if (!ok) return;
        vm.recordLogs();
        try router.fillFromPoolLiquidity(o) {} catch {}
        _tally(vm.getRecordedLogs());
    }

    /// Revoke or grant the Router, directly or by signature. Revoked makers can neither be filled nor create.
    function setExecutor(uint256 who, bool allow, bool bySig) external {
        calls++;
        hits[this.setExecutor.selector]++;
        uint256 a = who % actors.length;
        // keep grants the common case so the book stays busy
        allow = allow || (who % 4 != 0);
        if (!bySig) {
            vm.prank(actors[a]);
            hook.setExecutor(key.toId(), address(router), allow);
            return;
        }
        uint256 nonce = ++nonceCounter;
        uint256 deadline = block.timestamp + 1 hours;
        bytes32 structHash = OrderSignatures.hashSetExecutor(key, actors[a], address(router), allow, nonce, deadline);
        bytes memory sig =
            _sign(pks[a], keccak256(abi.encodePacked("\x19\x01", hook.DOMAIN_SEPARATOR(), structHash)));
        hook.setExecutorWithSig(key, actors[a], address(router), allow, nonce, deadline, sig);
    }

    function collect(bool zero) external {
        calls++;
        hits[this.collect.selector]++;
        FeeVault vault = hook.feeVault();
        vm.prank(protocolOwner);
        vault.collect(zero ? key.currency0 : key.currency1, protocolOwner);
    }

    /// Move time and blocks: derived salts change, signatures stay inside their deadlines.
    function warp(uint256 secs) external {
        calls++;
        hits[this.warp.selector]++;
        secs = bound(secs, 1, 600);
        vm.warp(block.timestamp + secs);
        vm.roll(block.number + 1);
    }
}

/// @dev Spec: `AsyncSwapProtocol/V2/Invariants.lean` (`Escrow`), `AsyncSwapSpec/RadixTree.lean`
///      (`PriceIndex.best_spec` = `invariant_bestPricesAgreeWithLinearScan`), `V2/Settlement.lean`
///      (hook balances untouched), `Priority.lean`.
///      Each check recomputes by brute force over every order the handler ever placed.
/// forge-config: default.invariant.runs = 48
/// forge-config: default.invariant.depth = 64
contract ProofInvariantTest is ProofBase {
    using PoolIdLibrary for PoolKey;
    using CurrencyLibrary for Currency;

    ProofHandler handler;

    function setUp() public virtual override {
        super.setUp();
        address[] memory as_ = new address[](4);
        uint256[] memory ks = new uint256[](4);
        as_[0] = maker;
        as_[1] = maker2;
        as_[2] = maker3;
        (as_[3], ks[3]) = makeAddrAndKey("fillerWithKey");
        ks[0] = makerPk;
        ks[1] = maker2Pk;
        ks[2] = maker3Pk;
        _fund(as_[3]);
        _grantRouter(as_[3]);
        handler = new ProofHandler(hook, router, protocolOwner, _handlerKey(), _priority(), as_, ks);
        targetContract(address(handler));
        bytes4[] memory selectors = new bytes4[](13);
        selectors[0] = ProofHandler.place.selector;
        selectors[1] = ProofHandler.placeWithSig.selector;
        selectors[2] = ProofHandler.fill.selector;
        selectors[3] = ProofHandler.cancel.selector;
        selectors[4] = ProofHandler.cancelWithSig.selector;
        selectors[5] = ProofHandler.reprice.selector;
        selectors[6] = ProofHandler.repriceWithSig.selector;
        selectors[7] = ProofHandler.matchBook.selector;
        selectors[8] = ProofHandler.liquidityFill.selector;
        selectors[9] = ProofHandler.setExecutor.selector;
        selectors[10] = ProofHandler.collect.selector;
        selectors[11] = ProofHandler.warp.selector;
        selectors[12] = ProofHandler.place.selector; // creates twice as likely
        targetSelector(FuzzSelector(address(handler), selectors));
    }

    function _handlerKey() internal view virtual returns (PoolKey memory) {
        return liqKey;
    }

    function _priority() internal pure virtual returns (bool) {
        return false;
    }

    /// @dev Distinct ids: a closed order frees its id, so a later order with the same (owner, direction, salt)
    ///      reuses it and `placed` can list it twice.
    function _ids() internal view returns (bytes32[] memory ids, bool[] memory zfo) {
        uint256 n = handler.placedCount();
        ids = new bytes32[](n);
        zfo = new bool[](n);
        uint256 m;
        for (uint256 i = 0; i < n; i++) {
            AsyncOrder memory o = handler.placedAt(i);
            bytes32 id = _id(o);
            bool seen;
            for (uint256 j = 0; j < m; j++) {
                if (ids[j] == id) seen = true;
            }
            if (seen) continue;
            ids[m] = id;
            zfo[m] = o.zeroForOne;
            ++m;
        }
        assembly ("memory-safe") {
            mstore(ids, m)
            mstore(zfo, m)
        }
    }

    /// @dev `escrowOf` summed over open orders (`V2/Invariants.lean` `owed`), for the hook's claims in `c`.
    function _owed(PoolKey memory k, bytes32[] memory ids, bool[] memory zfo, Currency c)
        internal
        view
        returns (uint256 total)
    {
        for (uint256 i = 0; i < ids.length; i++) {
            uint256 amountIn = hook.asyncOrder(k.toId(), ids[i]);
            if (amountIn == 0) continue;
            Currency input = zfo[i] ? k.currency0 : k.currency1;
            if (input == c) total += amountIn;
            if (c == usdc) total += hook.asyncOrderPriorityFee(k.toId(), ids[i]);
        }
    }

    /// `Escrow.claims`: for each currency the hook's claims equal the open orders' remaining input plus bids.
    function invariant_escrowEqualsOutstandingObligations() public view {
        PoolKey memory k = _handlerKey();
        (bytes32[] memory ids, bool[] memory zfo) = _ids();
        assertEq(_claims(k.currency0, address(hook)), _owed(k, ids, zfo, k.currency0), "currency0 escrow");
        assertEq(_claims(k.currency1, address(hook)), _owed(k, ids, zfo, k.currency1), "currency1 escrow");
    }

    /// `Escrow.wf`: open orders have positive input and positive outstanding minimum, the side the numeraire
    /// fixes and the spec's price key; the book's level counts cover exactly the open orders.
    function invariant_openOrdersWellFormed() public view {
        PoolKey memory k = _handlerKey();
        (bytes32[] memory ids, bool[] memory zfo) = _ids();
        uint256 open;
        for (uint256 i = 0; i < ids.length; i++) {
            (address owner, uint256 amountIn, uint256 amountOutMin, uint128 priceKey, bool isBuy,,) =
                hook.orderBookOrder(k.toId(), ids[i]);
            if (amountIn == 0) continue;
            open++;
            assertTrue(owner != address(0), "owner recorded");
            assertGt(amountOutMin, 0, "positive outstanding minimum");
            Currency input = zfo[i] ? k.currency0 : k.currency1;
            assertEq(isBuy, input == usdc, "a buy spends the numeraire");
            assertEq(priceKey, _specPriceKey(isBuy, amountIn, amountOutMin), "price key");
            uint256 bid = hook.asyncOrderPriorityFee(k.toId(), ids[i]);
            if (!_priority()) assertEq(bid, 0, "FIFO books carry no bids");
        }
        assertEq(open, _openCount(k, ids), "level counts = open orders");
    }

    /// `PriceIndex.best_spec`: the index returns the exact best price on each side, and the order it names is
    /// at that price and out-ranked by no other order there (bid first, then FIFO).
    function invariant_bestPricesAgreeWithLinearScan() public view {
        PoolKey memory k = _handlerKey();
        (bytes32[] memory ids,) = _ids();
        _checkSide(k, ids, true);
        _checkSide(k, ids, false);
    }

    function _scan(PoolKey memory k, bytes32[] memory ids, bool buySide)
        internal
        view
        returns (bool any, uint128 scan, uint256 atScan)
    {
        scan = buySide ? 0 : type(uint128).max;
        for (uint256 i = 0; i < ids.length; i++) {
            (, uint256 amountIn,, uint128 priceKey, bool isBuy,,) = hook.orderBookOrder(k.toId(), ids[i]);
            if (amountIn == 0 || isBuy != buySide) continue;
            any = true;
            if (buySide ? priceKey > scan : priceKey < scan) scan = priceKey;
        }
        for (uint256 i = 0; i < ids.length; i++) {
            (, uint256 amountIn,, uint128 priceKey, bool isBuy,,) = hook.orderBookOrder(k.toId(), ids[i]);
            if (amountIn != 0 && isBuy == buySide && priceKey == scan) ++atScan;
        }
    }

    function _checkSide(PoolKey memory k, bytes32[] memory ids, bool buySide) internal view {
        (bool found, uint128 bestKey, bytes32 bestId, address bestMaker) = hook.bestOrder(k.toId(), buySide);
        (bool any, uint128 scan, uint256 atScan) = _scan(k, ids, buySide);
        assertEq(found, any, "best exists iff a live order on that side");
        if (!any) {
            assertEq(bestId, bytes32(0));
            return;
        }
        assertEq(bestKey, scan, "best price");
        _checkBestOrder(k, bestId, bestMaker, buySide, scan);
        (bytes32 head,, uint32 count) = hook.orderBookLevel(k.toId(), buySide, scan);
        assertEq(head, bestId, "best order heads its level");
        assertEq(count, atScan, "level count = live orders at the best price");
        if (_priority()) _checkPriorityRank(k, ids, bestId, buySide, scan);
        else _checkFifoList(k, buySide, scan, count);
    }

    function _checkBestOrder(PoolKey memory k, bytes32 bestId, address bestMaker, bool buySide, uint128 scan)
        internal
        view
    {
        (address owner, uint256 amountIn,, uint128 priceKey, bool isBuy,,) = hook.orderBookOrder(k.toId(), bestId);
        assertGt(amountIn, 0, "best order is live");
        assertEq(owner, bestMaker, "best maker");
        assertEq(isBuy, buySide, "best order on its side");
        assertEq(priceKey, scan, "best order sits at the best price");
    }

    /// PriorityFee: no live order at the best price carries a larger remaining bid. Ties are ranked by
    /// sequence, which official does not expose, so the FIFO half of the tie-break is not checked here.
    function _checkPriorityRank(PoolKey memory k, bytes32[] memory ids, bytes32 bestId, bool buySide, uint128 scan)
        internal
        view
    {
        uint256 bestBid = hook.asyncOrderPriorityFee(k.toId(), bestId);
        for (uint256 i = 0; i < ids.length; i++) {
            if (ids[i] == bestId) continue;
            (, uint256 amountIn,, uint128 priceKey, bool isBuy,,) = hook.orderBookOrder(k.toId(), ids[i]);
            if (amountIn == 0 || isBuy != buySide || priceKey != scan) continue;
            assertGe(bestBid, hook.asyncOrderPriorityFee(k.toId(), ids[i]), "bid first");
        }
    }

    /// FIFO: the level is a well-linked list from head to tail of exactly `count` live orders at that price
    /// (sequence itself is not exposed by official, so "earliest" is checked as list order).
    // This check found a bug in v2, now fixed: it failed on every FIFO suite because after a reprice (or a
    // price-changing partial fill) the re-appended order kept its old `next` pointer, so walking a level reaches orders of another price or closed orders
    // ("listed order at the level price" / "listed order is live"). `AsyncFiller._append` now clears
    // `order.next`. Deterministic reproduction: Matching.t.sol
    // `test_reprice_reentersLast_keepsLevelListsWellFormed`. The PriorityFee suites (no linked list) pass.
    function _checkFifoList(PoolKey memory k, bool buySide, uint128 scan, uint32 count) internal view {
        (bytes32 head, bytes32 tail,) = hook.orderBookLevel(k.toId(), buySide, scan);
        bytes32 prev;
        bytes32 cur = head;
        uint256 n;
        while (cur != bytes32(0)) {
            bytes32 next = _checkListed(k, cur, prev, buySide, scan);
            prev = cur;
            cur = next;
            ++n;
            require(n <= count, "list longer than count");
        }
        assertEq(prev, tail, "tail");
        assertEq(n, count, "list length");
    }

    function _checkListed(PoolKey memory k, bytes32 cur, bytes32 prev, bool buySide, uint128 scan)
        internal
        view
        returns (bytes32 next)
    {
        (, uint256 amountIn,, uint128 priceKey, bool isBuy, bytes32 previous, bytes32 next_) =
            hook.orderBookOrder(k.toId(), cur);
        assertGt(amountIn, 0, "listed order is live");
        assertEq(priceKey, scan, "listed order at the level price");
        assertEq(isBuy, buySide, "listed order on the level side");
        assertEq(previous, prev, "back pointer");
        return next_;
    }

    /// The handler must actually be exercising the book, or the invariants above are vacuous.
    function afterInvariant() public view {
        assertGt(handler.calls(), 0, "handler never called");
    }

    /// The hook never holds tokens of its own: every leg is settled through the PoolManager.
    function invariant_hookHoldsNoTokens() public view {
        assertEq(_bal(currency0, address(hook)), 0);
        assertEq(_bal(currency1, address(hook)), 0);
        assertEq(_bal(other, address(hook)), 0);
        assertEq(address(hook).balance, 0);
        assertEq(_bal(currency0, address(router)), 0, "router keeps nothing either");
        assertEq(_bal(currency1, address(router)), 0);
        assertEq(_bal(other, address(router)), 0);
    }

    /// Backing: the PoolManager's balance covers every claim it issued (the full `Backing` equation needs the
    /// pool's reserves, which are not observable; the inequality is the observable half).
    function invariant_claimsBacked() public view {
        Currency[3] memory cs = [currency0, currency1, other];
        for (uint256 c; c < 3; ++c) {
            uint256 claims = _claims(cs[c], address(hook)) + _claims(cs[c], address(vault));
            for (uint256 i; i < handler.actorCount(); ++i) {
                claims += _claims(cs[c], handler.actorAt(i));
            }
            assertGe(_bal(cs[c], address(manager)), claims, "claims backed");
        }
    }
}

/// @dev PriorityFee book, numeraire as currency1.
/// forge-config: default.invariant.runs = 48
/// forge-config: default.invariant.depth = 64
contract ProofInvariantPriorityTest is ProofInvariantTest {
    function _handlerKey() internal view override returns (PoolKey memory) {
        return prioKey;
    }

    function _priority() internal pure override returns (bool) {
        return true;
    }
}

/// @dev The numeraire as currency0: a buy is `zeroForOne`, bids are paid and donated in currency0.
/// forge-config: default.invariant.runs = 48
/// forge-config: default.invariant.depth = 64
contract ProofInvariantFlipTest is ProofInvariantTest {
    function _handlerKey() internal view override returns (PoolKey memory) {
        return flipLiqKey;
    }
}

/// forge-config: default.invariant.runs = 48
/// forge-config: default.invariant.depth = 64
contract ProofInvariantFlipPriorityTest is ProofInvariantTest {
    function _handlerKey() internal view override returns (PoolKey memory) {
        return flipPrioKey;
    }

    function _priority() internal pure override returns (bool) {
        return true;
    }
}

/// @dev FIFO book with no pool liquidity: nothing leaves through the pool fallback, so orders rest and match.
/// forge-config: default.invariant.runs = 48
/// forge-config: default.invariant.depth = 64
contract ProofInvariantNoLiquidityTest is ProofInvariantTest {
    function _handlerKey() internal view override returns (PoolKey memory) {
        return key;
    }
}

/// @dev PriorityFee book with no pool liquidity: every bid is forfeited to the vault instead of donated.
/// forge-config: default.invariant.runs = 48
/// forge-config: default.invariant.depth = 64
contract ProofInvariantPriorityNoLiquidityTest is ProofInvariantTest {
    function _handlerKey() internal view override returns (PoolKey memory) {
        return emptyKey;
    }

    function _priority() internal pure override returns (bool) {
        return true;
    }
}
