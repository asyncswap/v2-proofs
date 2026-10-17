// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {Vm} from "forge-std/Test.sol";
import {AsyncSwap} from "@async-swap/AsyncSwap.sol";
import {AsyncOrder} from "@async-swap/types/AsyncOrder.sol";
import {ProofBase} from "./ProofBase.sol";

/// @dev Spec: `AsyncSwapSpec/Match.lean`.
///      Official `_matchAmounts` is private and reads storage, so each property is checked end to end: a resting
///      order and a crossing incoming order on a liquidity-free FIFO pool, the leg read from the hook's
///      `AsyncOrdersMatched(poolId, sellId, buyId, assetAmount, numeraireAmount)` event.
contract ProofAsyncMatchingTest is ProofBase {
    uint256 constant MAX = 1e24; // the makers' funding (the rebuild bounded by uint128 on a pure function)

    /// @dev Places the resting side first, then the incoming side; returns the first leg, if any.
    function _match(uint256 sellIn, uint256 sellMin, uint256 buyIn, uint256 buyMin, bool restingBuy)
        internal
        returns (bool matched, uint256 asset, uint256 quote)
    {
        AsyncOrder memory s = _sell(key, maker, sellIn, sellMin, 0);
        AsyncOrder memory b = _buy(key, maker2, buyIn, buyMin, 0);
        _place(restingBuy ? b : s);
        vm.recordLogs();
        vm.prank(restingBuy ? s.owner : b.owner);
        router.swap(restingBuy ? s : b, _userData(restingBuy ? s : b));
        Vm.Log[] memory logs = vm.getRecordedLogs();
        for (uint256 i; i < logs.length; ++i) {
            if (logs[i].emitter == address(hook) && logs[i].topics[0] == AsyncSwap.AsyncOrdersMatched.selector) {
                (asset, quote) = abi.decode(logs[i].data, (uint256, uint256));
                return (true, asset, quote);
            }
        }
    }

    /// `matchAmounts_sound`: a non-zero match never overspends either escrow and never executes either side
    /// below its limit price; `matchAmounts_cross`: therefore the limits cross.
    function testFuzz_sound(uint256 sellIn, uint256 sellMin, uint256 buyIn, uint256 buyMin, bool restingBuy) public {
        sellIn = bound(sellIn, 1, MAX);
        sellMin = bound(sellMin, 1, MAX);
        buyIn = bound(buyIn, 1, MAX);
        buyMin = bound(buyMin, 1, MAX);
        (bool matched, uint256 asset, uint256 quote) = _match(sellIn, sellMin, buyIn, buyMin, restingBuy);
        if (!matched) return;
        assertTrue(asset != 0 && quote != 0, "a leg moves both sides");
        assertLe(asset, sellIn, "asset_le_sell_escrow");
        assertLe(quote, buyIn, "quote_le_buy_escrow");
        assertLe(asset * sellMin, quote * sellIn, "seller_limit");
        assertLe(quote * buyMin, asset * buyIn, "buyer_limit");
        assertLe(buyMin * sellMin, buyIn * sellIn, "limits cross");
    }

    /// `matchAmounts_restingBuy_tight` / `matchAmounts_restingSell_tight`: the resting side is favoured by
    /// strictly less than one unit of its output.
    function testFuzz_tight(uint256 sellIn, uint256 sellMin, uint256 buyIn, uint256 buyMin, bool restingBuy) public {
        sellIn = bound(sellIn, 1, MAX);
        sellMin = bound(sellMin, 1, MAX);
        buyIn = bound(buyIn, 1, MAX);
        buyMin = bound(buyMin, 1, MAX);
        (bool matched, uint256 asset, uint256 quote) = _match(sellIn, sellMin, buyIn, buyMin, restingBuy);
        if (!matched) return;
        if (restingBuy) assertLt(asset * buyIn, quote * buyMin + buyIn);
        else assertLt(quote * sellIn, asset * sellMin + sellIn);
    }

    function test_exactCross() public {
        // seller: 1 asset for ≥ 2 quote; buyer: 2 quote for ≥ 1 asset; seller rests.
        (bool m, uint256 asset, uint256 quote) = _match(1e18, 2e18, 2e18, 1e18, false);
        assertTrue(m);
        assertEq(asset, 1e18);
        assertEq(quote, 2e18);
    }

    function test_exactCross_buyerRests() public {
        (bool m, uint256 asset, uint256 quote) = _match(1e18, 2e18, 2e18, 1e18, true);
        assertTrue(m);
        assertEq(asset, 1e18);
        assertEq(quote, 2e18);
    }

    function test_noCrossIsNoMatch() public {
        // seller asks 3, buyer bids 2.
        (bool m,,) = _match(1e18, 3e18, 2e18, 1e18, false);
        assertFalse(m);
    }

    function test_noCrossIsNoMatch_buyerRests() public {
        (bool m,,) = _match(1e18, 3e18, 2e18, 1e18, true);
        assertFalse(m);
    }

    /// The resting side's price sizes the trade: a seller resting at 2 against a buyer bidding 3 trades at 2.
    function test_restingPriceSizesTrade() public {
        (bool m, uint256 asset, uint256 quote) = _match(1e18, 2e18, 3e18, 1e18, false);
        assertTrue(m);
        assertEq(asset, 1e18);
        assertEq(quote, 2e18);
    }

    /// Buyer resting at 3: the seller gets 3.
    function test_restingPriceSizesTrade_buyerRests() public {
        (bool m, uint256 asset, uint256 quote) = _match(1e18, 2e18, 3e18, 1e18, true);
        assertTrue(m);
        assertEq(asset, 1e18);
        assertEq(quote, 3e18);
    }
}
