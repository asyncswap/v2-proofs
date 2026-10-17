// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {Currency, CurrencyLibrary} from "v4-core/types/Currency.sol";
import {IHooks} from "v4-core/interfaces/IHooks.sol";
import {PoolIdLibrary, PoolKey} from "v4-core/types/PoolKey.sol";
import {AsyncSwap} from "@async-swap/AsyncSwap.sol";
import {FeeVault} from "@async-swap/FeeVault.sol";
import {AsyncOrder} from "@async-swap/types/AsyncOrder.sol";
import {AsyncFiller} from "@async-swap/libraries/AsyncFiller.sol";
import {MockERC20} from "../utils/MockERC20.sol";
import {ProofBase} from "./ProofBase.sol";

/// @dev Create / fill / cancel / native / admin. Spec: `AsyncSwapProtocol/V2/Model.lean`, `V2/Settlement.lean`
///      (`fill_settlement`, `cancel_settlement`, `redeem_settlement`), `AsyncSwapSpec/Book.lean`, `Admin.lean`.
contract ProofLifecycleTest is ProofBase {
    using PoolIdLibrary for PoolKey;
    using CurrencyLibrary for Currency;

    /* ───────────────────────────────────── create ───────────────────────────────────── */

    function test_create_escrowsInputAsClaims() public {
        AsyncOrder memory o = _sell(key, maker, 1e18, 2e18, 0);
        bytes32 expected = idHarness.orderId(o);
        uint256 before = _bal(currency0, maker);
        bytes32 id = _place(o);

        // maker-chosen salt: the id is the one computed before sending
        assertEq(id, expected);
        assertEq(_bal(currency0, maker), before - 1e18);
        assertEq(_claims(currency0, address(hook)), 1e18, "escrow is the hook's claim");
        (address owner, uint256 amountIn, uint256 amountOutMin, uint128 priceKey, bool isBuy,,) =
            hook.orderBookOrder(key.toId(), id);
        assertEq(owner, maker);
        assertFalse(isBuy, "spends the asset: a sell");
        assertEq(amountIn, 1e18);
        assertEq(amountOutMin, 2e18);
        assertEq(priceKey, 2e18);
        // `sequence == 1` is not observable: official exposes no sequence; the level holds exactly this order.
        (bytes32 head, bytes32 tail, uint32 count) = hook.orderBookLevel(key.toId(), false, 2e18);
        assertEq(head, id);
        assertEq(tail, id);
        assertEq(count, 1);
        (bytes32 bestAsk, uint128 askKey) = _best(key, false);
        assertEq(bestAsk, id);
        assertEq(askKey, 2e18);
    }

    /// `created_order_escrowed`: the bid is the hook's numeraire claim as soon as the create unlock ends.
    function test_create_bidEscrowedInSameUnlock() public {
        AsyncOrder memory o = _sell(prioKey, maker, 1e18, 2e18, 5e6);
        uint256 before1 = _bal(currency1, maker);
        bytes32 id = _place(o);
        assertEq(_bal(currency1, maker), before1 - 5e6);
        assertEq(_claims(currency1, address(hook)), 5e6);
        assertEq(hook.asyncOrderPriorityFee(prioKey.toId(), id), 5e6);
    }

    function test_create_modeGuards() public {
        // FIFO book: no bids.
        AsyncOrder memory a = _sell(key, maker, 1e18, 2e18, 5e6);
        vm.expectRevert();
        this.place(a);
        // PriorityFee book: at least MIN_PRIORITY_FEE.
        a = _sell(prioKey, maker, 1e18, 2e18, 0);
        vm.expectRevert();
        this.place(a);
        a = _sell(prioKey, maker, 1e18, 2e18, 99_999);
        vm.expectRevert();
        this.place(a);
        _place(_sell(prioKey, maker, 1e18, 2e18, 100_000));
    }

    function place(AsyncOrder memory o) external returns (bytes32) {
        return _place(o);
    }

    function test_create_requiresExecutorGrant() public {
        vm.prank(maker);
        hook.setExecutor(key.toId(), address(router), false);
        AsyncOrder memory a = _sell(key, maker, 1e18, 2e18, 0);
        vm.expectRevert();
        this.place(a);
    }

    function test_create_onlyOwnerSubmits() public {
        AsyncOrder memory o = _sell(key, maker, 1e18, 2e18, 0);
        bytes memory data = _userData(o);
        vm.prank(maker2);
        vm.expectRevert(bytes("Only owner can swap"));
        router.swap(o, data);
    }

    function test_create_zeroAmountsRejected() public {
        AsyncOrder memory a = _sell(key, maker, 0, 2e18, 0);
        vm.expectRevert();
        this.place(a);
        a = _sell(key, maker, 1e18, 0, 0);
        vm.expectRevert();
        this.place(a);
    }

    /// The salt collision walk: the same salt twice yields two distinct open orders.
    function test_create_saltCollisionWalk() public {
        AsyncOrder memory o = _order(key, maker, true, 1e18, 2e18, 0, bytes32(uint256(1)));
        bytes32 id1 = _place(o);
        o.salt = bytes32(uint256(1));
        bytes32 id2 = _place(o);
        assertNotEq(id1, id2);
        assertTrue(_open(key, id1) && _open(key, id2));
        (,, uint32 count) = hook.orderBookLevel(key.toId(), false, 2e18);
        assertEq(count, 2);
    }

    /* ────────────────────────────────────── fill ────────────────────────────────────── */

    /// `fill_settlement`, `fill_fee_is_30bps`, `fill_output_conserved`.
    function test_fill_settlement() public {
        AsyncOrder memory o = _sell(key, maker, 1e18, 2e18, 0);
        bytes32 id = _place(o);
        uint256 fee = _poolFee(2e18);
        uint256 live = 2e18 + fee;

        uint256 maker1 = _bal(currency1, maker);
        uint256 filler0 = _bal(currency0, filler);
        uint256 filler1 = _bal(currency1, filler);

        // official `fillOrder` returns nothing; amounts are observed on balances.
        _fill(o, filler);
        assertEq(fee, 3 * live / 1000, "30 bps of gross");

        assertEq(_bal(currency1, maker), maker1 + 2e18, "maker receives the stored minimum");
        assertEq(_bal(currency1, filler), filler1 - live, "filler pays live gross");
        assertEq(_bal(currency0, filler), filler0 + 1e18, "filler receives the escrow");
        assertEq(_claims(currency1, address(vault)), fee, "vault receives the fee as claims");
        assertEq(_claims(currency0, address(hook)), 0);
        assertEq(_bal(currency0, address(hook)), 0);
        assertEq(_bal(currency1, address(hook)), 0);
        assertFalse(_open(key, id));
        (bool found,,,) = hook.bestOrder(key.toId(), false);
        assertFalse(found, "book empty");
    }

    /// `fillOrder_ignores_calldata_amounts`: a stale struct cannot underpay the maker.
    function test_fill_usesStoredTerms() public {
        AsyncOrder memory o = _sell(key, maker, 1e18, 2e18, 0);
        _place(o);
        AsyncOrder memory stale = _sell(key, maker, 1e18, 2e18, 0);
        stale.salt = o.salt;
        stale.amountOutMin = 1; // not part of the id
        uint256 maker1 = _bal(currency1, maker);
        vm.prank(filler);
        router.fillOrder(stale, type(uint256).max, "");
        assertEq(_bal(currency1, maker), maker1 + 2e18);
    }

    function test_fill_respectsMaxPrice() public {
        AsyncOrder memory o = _sell(key, maker, 1e18, 2e18, 0);
        _place(o);
        uint256 live = 2e18 + _poolFee(2e18);
        vm.prank(filler);
        // official: a require string, not `PriceAboveMax(live, max)`
        vm.expectRevert(bytes("Price exceeds maxPrice"));
        router.fillOrder(o, live - 1, "");
    }

    /// `fill_requires_grant`: a maker who revoked the router cannot be filled through it.
    function test_fill_requiresExecutorGrant() public {
        AsyncOrder memory o = _sell(key, maker, 1e18, 2e18, 0);
        _place(o);
        vm.prank(maker);
        hook.setExecutor(key.toId(), address(router), false);
        vm.prank(filler);
        vm.expectRevert(AsyncFiller.NotAuthorizedExecutor.selector);
        router.fillOrder(o, type(uint256).max, "");
    }

    /// `fill_closes`: a filled order cannot be filled or cancelled again.
    function test_fill_closes() public {
        AsyncOrder memory o = _sell(key, maker, 1e18, 2e18, 0);
        _place(o);
        _fill(o, filler);
        vm.prank(filler);
        vm.expectRevert();
        router.fillOrder(o, type(uint256).max, "");
        vm.prank(maker);
        vm.expectRevert();
        router.cancelOrder(o);
    }

    /// The bid of a filled order is donated to active LPs (pool reserves grow, hook claims fall), never refunded.
    function test_fill_donatesBid() public {
        AsyncOrder memory o = _sell(prioKey, maker, 1e18, 2e18, 5e6);
        _place(o);
        uint256 pm1 = _bal(currency1, address(manager));
        uint256 maker1 = _bal(currency1, maker);
        _fill(o, filler);
        assertEq(_claims(currency1, address(hook)), 0, "bid left the hook");
        assertEq(_claims(currency1, address(vault)), _poolFee(2e18), "donated, not forfeited");
        assertEq(_bal(currency1, maker), maker1 + 2e18, "bid not refunded");
        // PoolManager keeps the bid (donated) plus the fee claim backing, minus nothing.
        assertEq(_bal(currency1, address(manager)), pm1 + _poolFee(2e18) + 2e18 - 2e18);
    }

    /// With no liquidity the bid is forfeited to the vault.
    function test_fill_forfeitsBidWithoutLiquidity() public {
        AsyncOrder memory o = _sell(emptyKey, maker, 1e18, 2e18, 5e6);
        _place(o);
        _fill(o, filler);
        assertEq(_claims(currency1, address(vault)), _poolFee(2e18) + 5e6);
        assertEq(_claims(currency1, address(hook)), 0);
    }

    /* ───────────────────────────────────── cancel ───────────────────────────────────── */

    /// `cancel_settlement`: exactly the remaining escrow back; the bid is settled, not refunded.
    function test_cancel_settlement() public {
        // bid 2 quote for ≥ 3 asset: the 1:1 pool cannot meet it, so it rests (official pool fallback).
        AsyncOrder memory o = _buy(prioKey, maker, 2e18, 3e18, 5e6);
        bytes32 id = _place(o);
        assertEq(_claims(currency1, address(hook)), 2e18 + 5e6);
        uint256 maker1 = _bal(currency1, maker);
        vm.prank(maker);
        router.cancelOrder(o);
        assertEq(_bal(currency1, maker), maker1 + 2e18, "exactly the remaining input back");
        assertEq(_claims(currency1, address(hook)), 0);
        assertFalse(_open(prioKey, id));
        (bool found,,,) = hook.bestOrder(prioKey.toId(), true);
        assertFalse(found);
    }

    function test_cancel_onlyOwner() public {
        AsyncOrder memory o = _sell(key, maker, 1e18, 2e18, 0);
        _place(o);
        vm.prank(maker2);
        vm.expectRevert(bytes("Only owner can cancel"));
        router.cancelOrder(o);
    }

    /// `no_unauthorized_close`: neither fill nor cancel without the maker's grant, directly on the hook either.
    function test_cancel_directCallNeedsOwnerOrExecutor() public {
        AsyncOrder memory o = _sell(key, maker, 1e18, 2e18, 0);
        _place(o);
        vm.prank(maker2);
        // official checks the executor before touching the PoolManager (rebuild: `NotUnlocked`)
        vm.expectRevert(AsyncFiller.NotAuthorizedExecutor.selector);
        hook.cancelOrder(o);
        vm.prank(maker2);
        vm.expectRevert(AsyncFiller.NotAuthorizedExecutor.selector);
        hook.executeOrder(o, abi.encode(maker2));
    }

    /* ───────────────────────────────────── native ───────────────────────────────────── */

    /// Native input: the escrow is native; a fill pays it to the filler as ERC-6909 claims of currency0,
    /// redeemable through `NativeClaims` (`redeem_settlement`).
    function test_native_input_fill_and_redeem() public {
        AsyncOrder memory o = _sell(nativeKey, maker, 1 ether, 2e18, 0);
        uint256 makerEth = maker.balance;
        bytes32 id = _place(o);
        assertEq(maker.balance, makerEth - 1 ether);
        assertEq(_claims(CurrencyLibrary.ADDRESS_ZERO, address(hook)), 1 ether);
        assertEq(address(router).balance, 0);

        uint256 maker1 = _bal(currency1, maker);
        _fill(o, filler);
        assertFalse(_open(nativeKey, id));
        assertEq(_bal(currency1, maker), maker1 + 2e18);
        assertEq(_claims(CurrencyLibrary.ADDRESS_ZERO, filler), 1 ether, "filler paid in native claims");
        assertEq(_claims(CurrencyLibrary.ADDRESS_ZERO, address(hook)), 0);

        address recipient = makeAddr("recipient");
        vm.startPrank(filler);
        manager.setOperator(address(nativeClaims), true);
        nativeClaims.redeem(recipient, 1 ether); // official argument order: (recipient, amount)
        vm.stopPrank();
        assertEq(recipient.balance, 1 ether);
        assertEq(_claims(CurrencyLibrary.ADDRESS_ZERO, filler), 0);
    }

    /// Native output: the filler's `msg.value` is exactly the live price; the maker is paid in native claims;
    /// the fee is a native claim of the vault; the hook keeps no ETH (`fill_settlement`: hook balances untouched).
    function test_native_output_fill() public {
        AsyncOrder memory o = _buy(nativeKey, maker, 2e18, 1 ether, 0);
        bytes32 id = _place(o);
        uint256 fee = _poolFee(1 ether);
        uint256 live = 1 ether + fee;

        vm.prank(filler);
        vm.expectRevert(bytes("msg.value != livePrice"));
        router.fillOrder{value: live - 1}(o, live, "");

        uint256 fillerEth = filler.balance;
        uint256 filler1 = _bal(currency1, filler);
        vm.prank(filler);
        router.fillOrder{value: live}(o, live, "");
        assertFalse(_open(nativeKey, id));
        assertEq(filler.balance, fillerEth - live);
        assertEq(_bal(currency1, filler), filler1 + 2e18);
        assertEq(_claims(CurrencyLibrary.ADDRESS_ZERO, maker), 1 ether);
        assertEq(_claims(CurrencyLibrary.ADDRESS_ZERO, address(vault)), fee);
        assertEq(address(hook).balance, 0);
        // `pendingNativeDeposit()` is not exposed by official (a private transient slot); the zero hook
        // balance above is the observable half.
    }

    function test_native_cancel_refundsAsClaims() public {
        AsyncOrder memory o = _sell(nativeKey, maker, 1 ether, 2e18, 0);
        _place(o);
        vm.prank(maker);
        router.cancelOrder(o);
        assertEq(_claims(CurrencyLibrary.ADDRESS_ZERO, maker), 1 ether);
        assertEq(_claims(CurrencyLibrary.ADDRESS_ZERO, address(hook)), 0);
    }

    function test_native_swapRequiresExactValue() public {
        AsyncOrder memory o = _sell(nativeKey, maker, 1 ether, 2e18, 0);
        bytes memory data = _userData(o);
        vm.prank(maker);
        vm.expectRevert(bytes("msg.value != order.amountIn"));
        router.swap{value: 0.5 ether}(o, data);
        AsyncOrder memory e = _sell(key, maker, 1e18, 2e18, 0);
        data = _userData(e);
        vm.prank(maker);
        vm.expectRevert(bytes("msg.value forbidden for ERC20 input"));
        router.swap{value: 1}(e, data);
    }

    /* ─────────────────────────────────────── admin ─────────────────────────────────────── */

    /// `collect_settlement`: owner-only; moves exactly the vault's claims; no order or hook claim touched.
    function test_feeVault_collect() public {
        AsyncOrder memory o = _sell(key, maker, 1e18, 2e18, 0);
        _place(o);
        AsyncOrder memory o2 = _sell(key, maker2, 1e18, 3e18, 0);
        bytes32 id2 = _place(o2);
        _fill(o, filler);
        uint256 fee = _poolFee(2e18);
        address recipient = makeAddr("treasury");

        vm.prank(filler);
        vm.expectRevert(FeeVault.Unauthorized.selector);
        vault.collect(currency1, recipient);

        vm.prank(protocolOwner);
        vault.collect(currency1, recipient); // official returns nothing
        assertEq(_bal(currency1, recipient), fee);
        assertEq(_claims(currency1, address(vault)), 0);
        assertEq(_claims(currency0, address(hook)), 1e18, "maker2's escrow untouched");
        assertTrue(_open(key, id2));
    }

    /// `owner_change_only_via_accept`, `transfer_requires_owner`, `accept_clears_pending`.
    function test_ownership_twoStep() public {
        address next = makeAddr("next");
        vm.prank(next);
        vm.expectRevert(AsyncSwap.NotOwner.selector);
        hook.transferOwnership(next);
        vm.prank(protocolOwner);
        vm.expectRevert(AsyncSwap.ZeroAddress.selector);
        hook.transferOwnership(address(0));
        vm.prank(protocolOwner);
        hook.transferOwnership(next);
        assertEq(hook.owner(), protocolOwner, "nominating does not transfer control");
        vm.prank(maker);
        vm.expectRevert(AsyncSwap.NotOwner.selector);
        hook.acceptOwnership();
        vm.prank(next);
        hook.acceptOwnership();
        assertEq(hook.owner(), next);
        assertEq(hook.pendingOwner(), address(0));
    }

    /// `sweep_settlement`: moves only the hook's own balance, never claims.
    function test_sweep() public {
        _place(_sell(key, maker, 1e18, 2e18, 0));
        MockERC20(Currency.unwrap(currency0)).mint(address(hook), 7e18);
        vm.prank(maker);
        vm.expectRevert(AsyncSwap.NotOwner.selector);
        hook.sweep(currency0, maker);
        address to = makeAddr("sweepTo");
        vm.prank(protocolOwner);
        hook.sweep(currency0, to); // official returns nothing
        assertEq(_bal(currency0, to), 7e18);
        assertEq(_bal(currency0, address(hook)), 0);
        assertEq(_claims(currency0, address(hook)), 1e18, "escrow claims untouched");
    }

    function test_setOrderingMode_requiresEmptyBook() public {
        _place(_sell(key, maker, 1e18, 2e18, 0));
        vm.prank(protocolOwner);
        vm.expectRevert(AsyncFiller.InvalidOrderingModeChange.selector);
        hook.setOrderingMode(key, AsyncFiller.OrderingMode.PriorityFee);
        vm.prank(maker);
        vm.expectRevert(AsyncSwap.NotOwner.selector);
        hook.setOrderingMode(emptyKey, AsyncFiller.OrderingMode.FIFO);
        vm.prank(protocolOwner);
        hook.setOrderingMode(emptyKey, AsyncFiller.OrderingMode.FIFO);
        assertEq(uint8(hook.orderingMode(emptyKey.toId())), uint8(AsyncFiller.OrderingMode.FIFO));
    }

    /// The Router only drives this hook. Official has no `WrongHook` check: an order keyed to a foreign hook
    /// reverts in the PoolManager (that pool does not exist), and nothing reaches this hook's book.
    function test_router_rejectsForeignHook() public {
        AsyncOrder memory o = _sell(key, maker, 1e18, 2e18, 0);
        o.key.hooks = IHooks(address(0xdead));
        bytes memory data = _userData(o);
        uint256 maker0 = _bal(currency0, maker);
        vm.prank(maker);
        vm.expectRevert();
        router.swap(o, data);
        assertEq(_bal(currency0, maker), maker0);
    }
}
