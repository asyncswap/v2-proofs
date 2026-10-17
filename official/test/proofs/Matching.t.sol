// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {Currency} from "v4-core/types/Currency.sol";
import {PoolId} from "v4-core/types/PoolId.sol";
import {PoolIdLibrary, PoolKey} from "v4-core/types/PoolKey.sol";
import {IPoolManager} from "v4-core/interfaces/IPoolManager.sol";
import {StateLibrary} from "v4-core/libraries/StateLibrary.sol";
import {AsyncSwap} from "@async-swap/AsyncSwap.sol";
import {AsyncOrder} from "@async-swap/types/AsyncOrder.sol";
import {AsyncFiller} from "@async-swap/libraries/AsyncFiller.sol";
import {AsyncMatching} from "@async-swap/libraries/AsyncMatching.sol";
import {ProofBase} from "./ProofBase.sol";

/// @dev Matching, priority, repricing, liquidity fills. Spec: `AsyncSwapSpec/Match.lean`, `Reduce.lean`
///      (`maker_limit_honored`, `runLegs_amountIn`, `runLegs_priorityFee`), `Priority.lean`,
///      `AsyncSwapProtocol/V2/Model.lean` (`matchLoop`, `matchBook`, `liquidityFillBody`).
contract ProofMatchingTest is ProofBase {
    using PoolIdLibrary for PoolKey;
    using StateLibrary for IPoolManager;

    /// A crossing order is matched in the create unlock: no fee, both closed, hook claims back to zero.
    function test_match_fullFill() public {
        AsyncOrder memory s = _sell(key, maker, 1e18, 2e18, 0);
        bytes32 sellId = _place(s);
        AsyncOrder memory b = _buy(key, maker2, 2e18, 1e18, 0);
        uint256 maker1 = _bal(currency1, maker);
        uint256 maker2_0 = _bal(currency0, maker2);

        // the maker-chosen salt makes the buy id known before sending
        vm.expectEmit(true, true, true, true, address(hook));
        emit AsyncSwap.AsyncOrdersMatched(key.toId(), sellId, idHarness.orderId(b), 1e18, 2e18);
        bytes32 buyId = _place(b);

        assertFalse(_open(key, sellId));
        assertFalse(_open(key, buyId));
        assertEq(_bal(currency1, maker), maker1 + 2e18);
        assertEq(_bal(currency0, maker2), maker2_0 + 1e18);
        assertEq(_claims(currency0, address(hook)), 0);
        assertEq(_claims(currency1, address(hook)), 0);
        assertEq(_claims(currency1, address(vault)), 0, "no protocol fee on matches");
        (bool found,,,) = hook.bestOrder(key.toId(), false);
        assertFalse(found);
        (found,,,) = hook.bestOrder(key.toId(), true);
        assertFalse(found);
    }

    function test_match_noCrossRests() public {
        bytes32 sellId = _place(_sell(key, maker, 1e18, 3e18, 0)); // ask 3
        bytes32 buyId = _place(_buy(key, maker2, 2e18, 1e18, 0)); // bid 2
        assertTrue(_open(key, sellId) && _open(key, buyId));
        assertEq(_claims(currency0, address(hook)), 1e18);
        assertEq(_claims(currency1, address(hook)), 2e18);
    }

    /// `maker_limit_honored` / `runLegs_amountIn`: across two partial legs the resting seller receives at
    /// least the minimum they signed and all of their input is consumed; the resting price sizes each leg.
    function test_match_partialFills_makerLimitHonored() public {
        AsyncOrder memory s = _sell(key, maker, 1e18, 2e18, 0); // ask 2
        bytes32 sellId = _place(s);
        bytes32 rival = _place(_sell(key, maker2, 1e18, 2e18, 0)); // same price, later
        uint256 maker1 = _bal(currency1, maker);

        bytes32 b1 = _place(_buy(key, maker2, 1e18, 0.5e18, 0)); // 1 quote at bid 2 → half the seller
        assertFalse(_open(key, b1));
        (uint256 amountIn, uint256 amountOutMin) = hook.asyncOrderInfo(key.toId(), sellId);
        assertEq(amountIn, 0.5e18);
        assertEq(amountOutMin, 1e18);
        assertEq(_priceKeyOf(key, sellId), 2e18, "price key unchanged");
        // `sequence == 1` is not exposed; time priority is observed as staying at the head of its level.
        (bytes32 head,,) = hook.orderBookLevel(key.toId(), false, 2e18);
        assertEq(head, sellId, "a partial fill that keeps the price keeps time priority");
        assertEq(_claims(currency0, address(hook)), 1.5e18);

        uint256 maker3_1 = _bal(currency1, maker3);
        bytes32 b2 = _place(_buy(key, maker3, 1.5e18, 0.5e18, 0)); // bid 3, but trades at the resting ask 2
        assertFalse(_open(key, sellId));
        // the buyer's minimum is met by 0.5 asset for 1 quote: it closes and the unused 0.5 quote is refunded
        assertFalse(_open(key, b2));
        assertEq(_bal(currency1, maker3), maker3_1 - 1e18, "buyer paid the resting price, rest refunded");
        assertEq(_bal(currency1, maker), maker1 + 2e18, "seller received exactly the signed minimum");
        assertEq(_claims(currency0, address(hook)), 1e18, "only the rival's escrow is left");
        assertEq(_claims(currency1, address(hook)), 0);
        assertTrue(_open(key, rival));
    }

    /// `bestAtPrice_priority` (PriorityFee mode): higher bid first, equal bids by earlier sequence.
    function test_priority_bidFirstThenFifo() public {
        bytes32 s1 = _place(_sell(prioKey, maker, 1e18, 2e18, 1e6));
        bytes32 s2 = _place(_sell(prioKey, maker2, 1e18, 2e18, 3e6));
        bytes32 s3 = _place(_sell(prioKey, maker3, 1e18, 2e18, 3e6));
        (bytes32 best,) = _best(prioKey, false);
        assertEq(best, s2);

        _place(_buy(prioKey, keeper, 2e18, 1e18, 1e5));
        assertFalse(_open(prioKey, s2));
        (best,) = _best(prioKey, false);
        assertEq(best, s3);

        _place(_buy(prioKey, keeper, 2e18, 1e18, 1e5));
        assertFalse(_open(prioKey, s3));
        (best,) = _best(prioKey, false);
        assertEq(best, s1);

        _place(_buy(prioKey, keeper, 2e18, 1e18, 1e5));
        assertFalse(_open(prioKey, s1));
        (bool found,,,) = hook.bestOrder(prioKey.toId(), false);
        assertFalse(found);
        assertEq(_claims(currency1, address(hook)), 0, "every bid settled");
    }

    /// `fifo_head_earliest` (FIFO mode).
    function test_fifo_earliestFirst() public {
        bytes32 s1 = _place(_sell(key, maker, 1e18, 2e18, 0));
        bytes32 s2 = _place(_sell(key, maker2, 1e18, 2e18, 0));
        (bytes32 best,) = _best(key, false);
        assertEq(best, s1);
        _place(_buy(key, keeper, 2e18, 1e18, 0));
        assertFalse(_open(key, s1));
        assertTrue(_open(key, s2));
    }

    /// `best_bid_is_max` / `best_ask_is_min`: the matched level is the best price.
    function test_match_bestPriceFirst() public {
        bytes32 askHigh = _place(_sell(key, maker, 1e18, 3e18, 0));
        bytes32 askLow = _place(_sell(key, maker2, 1e18, 2e18, 0));
        _place(_buy(key, keeper, 3e18, 1e18, 0)); // bid 3 crosses both; takes the lower ask first, at 2
        assertFalse(_open(key, askLow));
        assertTrue(_open(key, askHigh));
    }

    /// `reprice_sequence_last`: a repriced order re-enters behind every live order; `updatePrice_claims`.
    function test_reprice_reentersLast() public {
        AsyncOrder memory s1o = _sell(key, maker, 1e18, 2e18, 0);
        bytes32 s1 = _place(s1o);
        bytes32 s2 = _place(_sell(key, maker2, 1e18, 2e18, 0));
        uint256 claims0 = _claims(currency0, address(hook));
        vm.prank(maker);
        hook.updatePrice(s1o, 2e18);
        (bytes32 best,) = _best(key, false);
        assertEq(best, s2);
        // `sequence == 3` is not exposed; the re-entered order is the level's tail.
        (bytes32 head, bytes32 tail,) = hook.orderBookLevel(key.toId(), false, 2e18);
        assertEq(head, s2);
        assertEq(tail, s1);
        assertEq(_claims(currency0, address(hook)), claims0, "repricing moves no claims");
        // reprice to a new level
        vm.prank(maker);
        hook.updatePrice(s1o, 1e18);
        (best,) = _best(key, false);
        assertEq(best, s1);
        assertEq(_priceKeyOf(key, s1), 1e18);
    }

    function test_reprice_onlyOwnerAndNonZero() public {
        AsyncOrder memory s1o = _sell(key, maker, 1e18, 2e18, 0);
        _place(s1o);
        vm.prank(maker2);
        vm.expectRevert(AsyncFiller.NotOrderOwner.selector);
        hook.updatePrice(s1o, 1e18);
        vm.prank(maker);
        vm.expectRevert(AsyncFiller.ZeroAmount.selector);
        hook.updatePrice(s1o, 0);
    }

    /// `matchBook`: a book crossed by a reprice is matched by any keeper.
    function test_matchBook_keeper() public {
        AsyncOrder memory so = _sell(key, maker, 1e18, 3e18, 0);
        bytes32 sellId = _place(so);
        bytes32 buyId = _place(_buy(key, maker2, 2e18, 1e18, 0));
        vm.prank(maker);
        hook.updatePrice(so, 2e18); // now crossed, no automatic match
        assertTrue(_open(key, sellId) && _open(key, buyId));

        vm.recordLogs();
        vm.prank(keeper);
        router.matchBook(key, 8); // official returns nothing: count the matched events
        assertEq(_countMatches(), 1);
        assertFalse(_open(key, sellId));
        assertFalse(_open(key, buyId));
    }

    function test_matchBook_boundsMaxMatches() public {
        vm.prank(keeper);
        vm.expectRevert(AsyncMatching.InvalidMatchBound.selector);
        router.matchBook(key, 0);
        vm.prank(keeper);
        vm.expectRevert(AsyncMatching.InvalidMatchBound.selector);
        router.matchBook(key, 9);
        vm.recordLogs();
        vm.prank(keeper);
        router.matchBook(key, 8);
        assertEq(_countMatches(), 0);
    }

    /// At most `MAX_MATCHES_PER_CALL` matches per create.
    function test_match_capPerCall() public {
        bytes32[] memory ids = new bytes32[](11);
        for (uint256 i = 0; i < 10; i++) {
            ids[i] = _place(_sell(key, maker, 1e17, 2e17, 0));
        }
        ids[10] = _place(_buy(key, maker2, 10e18, 1e18, 0)); // crosses all ten, but only eight are matched
        assertEq(lastPlaceMatches, AsyncMatching.MAX_MATCHES_PER_CALL);
        assertEq(_openCount(key, ids), 3); // 2 sells + the partially filled buy
        vm.recordLogs();
        vm.prank(keeper);
        router.matchBook(key, 8);
        assertEq(_countMatches(), 2);
        assertEq(_openCount(key, ids), 0); // the tenth leg meets the buyer's minimum: closed, 8 quote refunded
        assertEq(_claims(currency1, address(hook)), 0);
    }

    /// `liquidityFill_meets_min`: the whole escrow is swapped through the pool; the maker is paid the output.
    /// Official fills from the pool automatically at create, so the order is placed while the pool is empty
    /// and liquidity is added afterwards.
    function test_fillFromPoolLiquidity() public {
        AsyncOrder memory s = _sell(key, maker, 1e15, 0.9e15, 0); // ask 0.9 at a 1:1 pool
        bytes32 id = _place(s);
        assertTrue(_open(key, id));
        _addLiquidity(key);
        uint256 maker1 = _bal(currency1, maker);
        vm.prank(keeper);
        router.fillFromPoolLiquidity(s);
        uint256 out = _bal(currency1, maker) - maker1;
        assertGe(out, 0.9e15);
        assertLt(out, 1e15);
        assertFalse(_open(key, id));
        assertEq(_claims(currency0, address(hook)), 0);
    }

    /// Official `fillFromPoolLiquidity` catches a failed attempt (v2's try/catch) instead of reverting: the
    /// limit is still never undercut, the order simply stays resting with its escrow.
    function test_fillFromPoolLiquidity_limitNotMet() public {
        AsyncOrder memory s = _sell(liqKey, maker, 1e15, 2e15, 0);
        bytes32 id = _place(s);
        uint256 maker1 = _bal(currency1, maker);
        vm.prank(keeper);
        router.fillFromPoolLiquidity(s);
        assertTrue(_open(liqKey, id));
        assertEq(_amountIn(liqKey, id), 1e15);
        assertEq(_bal(currency1, maker), maker1);
        assertEq(_claims(currency0, address(hook)), 1e15);
    }

    /// No active liquidity: likewise caught by official (`NoActiveLiquidity` stays internal); the order rests.
    function test_fillFromPoolLiquidity_noLiquidity() public {
        AsyncOrder memory s = _sell(emptyKey, maker, 1e15, 0.9e15, 1e6);
        bytes32 id = _place(s);
        vm.prank(keeper);
        router.fillFromPoolLiquidity(s);
        assertTrue(_open(emptyKey, id));
        assertEq(_claims(currency1, address(hook)), 1e6, "bid still escrowed");
    }

    /// `runLegs_priorityFee`: donated so far plus the remainder equals the original bid; the remainder is
    /// donated on close. The hook never keeps any part of a bid.
    function test_match_bidDonatedProRata() public {
        AsyncOrder memory so = _sell(prioKey, maker, 1e18, 2e18, 4e6);
        bytes32 sellId = _place(so);
        assertEq(_claims(currency1, address(hook)), 4e6);
        _place(_buy(prioKey, maker2, 1e18, 0.5e18, 1e5)); // half the seller
        assertEq(hook.asyncOrderPriorityFee(prioKey.toId(), sellId), 2e6, "half the bid donated");
        assertEq(_claims(currency1, address(hook)), 2e6 + 0, "the seller's remaining bid is the only claim left");
        _place(_buy(prioKey, maker3, 1e18, 0.5e18, 1e5));
        assertFalse(_open(prioKey, sellId));
        assertEq(_claims(currency1, address(hook)), 0);
        assertEq(_claims(currency1, address(vault)), 0, "liquidity present: donated, not forfeited");
    }

    /// `reprice_sequence_last` + `PriceIndex.best_spec`, deterministic reproduction of the invariant failure.
    /// Regression for a bug this suite found in v2 (fixed in `AsyncFiller._append`, which now clears `next`):
    /// a FIFO reprice left the order's stale `next` pointer, so the repriced order, as the tail of its new level, still links
    /// into its old level. Removing it then rewires the wrong level: the new level's tail points at a deleted
    /// order and, later, its head points at an order of another price (or a closed one). `bestOrder` then names
    /// a closed order and a crossed book can no longer be matched.
    function test_reprice_reentersLast_keepsLevelListsWellFormed() public {
        AsyncOrder memory c = _sell(key, maker, 1e18, 3e18, 0); // level 3: C
        bytes32 cId = _place(c);
        AsyncOrder memory a = _sell(key, maker, 1e18, 2e18, 0); // level 2: A, B
        bytes32 aId = _place(a);
        AsyncOrder memory b = _sell(key, maker2, 1e18, 2e18, 0);
        bytes32 bId = _place(b);

        vm.prank(maker);
        hook.updatePrice(a, 3e18); // level 3: C, A    level 2: B
        (,,,,, bytes32 aPrev, bytes32 aNext) = hook.orderBookOrder(key.toId(), aId);
        assertEq(aPrev, cId, "A re-entered behind C");
        // Before the fix A.next was still B, an order of the 2e18 level.
        assertEq(aNext, bytes32(0), "the tail of a level has no successor");

        vm.prank(maker);
        router.cancelOrder(a);
        AsyncOrder memory d = _sell(key, maker3, 1e18, 3e18, 0); // level 3 should be: C, D
        bytes32 dId = _place(d);
        vm.prank(maker);
        router.cancelOrder(c); // level 3 should be: D
        vm.prank(maker2);
        router.cancelOrder(b); // level 2 gone

        (bool found, uint128 askKey, bytes32 bestAsk, address bestMaker) = hook.bestOrder(key.toId(), false);
        assertTrue(found);
        assertEq(askKey, 3e18);
        // Before the fix the level head was B (cancelled, owner zero), not D.
        assertEq(bestAsk, dId, "best ask is the only live ask");
        assertEq(bestMaker, maker3);

        // A crossing bid (bid 4 > ask 3) and a keeper's matchBook must clear D.
        bytes32 eId = _place(_buy(key, maker2, 4e18, 1e18, 0));
        vm.prank(keeper);
        router.matchBook(key, 8);
        // Before the fix the crossed book was stuck: matching read the dead head B and stopped.
        assertFalse(_open(key, dId) && _open(key, eId), "a crossed book is matched");
    }
}
