// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {IHooks} from "v4-core/interfaces/IHooks.sol";
import {Hooks} from "v4-core/libraries/Hooks.sol";
import {LPFeeLibrary} from "v4-core/libraries/LPFeeLibrary.sol";
import {StateLibrary} from "v4-core/libraries/StateLibrary.sol";
import {IPoolManager} from "v4-core/interfaces/IPoolManager.sol";
import {CustomRevert} from "v4-core/libraries/CustomRevert.sol";
import {Currency} from "v4-core/types/Currency.sol";
import {PoolIdLibrary, PoolKey} from "v4-core/types/PoolKey.sol";
import {AsyncSwap} from "@async-swap/AsyncSwap.sol";
import {BaseHook} from "@async-swap/BaseHook.sol";
import {AsyncOrder} from "@async-swap/types/AsyncOrder.sol";
import {ProofBase} from "./ProofBase.sol";

/// @dev Only bypasses permission-address mining for the constructor rejection test.
contract ProofNumeraireConstructorHarness is AsyncSwap {
    constructor(IPoolManager manager_, Currency quote, address owner_) AsyncSwap(manager_, quote, owner_) {}

    function validateHookAddress(BaseHook) internal pure override {}
}

/// @dev The numeraire on either side of a pool. The Lean model fixes it as currency1; these tests run the same
///      flows on `flipKey` / `flipPrioKey`, where it is currency0, so a buy is `zeroForOne` and bids are
///      escrowed, donated and forfeited in currency0.
contract ProofNumeraireTest is ProofBase {
    using StateLibrary for IPoolManager;
    using PoolIdLibrary for PoolKey;

    function _wrappedInitError(bytes4 hookError) internal view returns (bytes memory) {
        return abi.encodeWithSelector(
            CustomRevert.WrappedError.selector,
            address(hook),
            IHooks.beforeInitialize.selector,
            abi.encodeWithSelector(hookError),
            abi.encodeWithSelector(Hooks.HookCallFailed.selector)
        );
    }

    /// Buy: spend `amountIn` of the numeraire (currency0 here) for at least `amountOutMin` of `other`.
    function _flipBuy(PoolKey memory k, address owner, uint256 amountIn, uint256 amountOutMin, uint256 fee)
        internal
        returns (AsyncOrder memory)
    {
        return _order(k, owner, true, amountIn, amountOutMin, fee, _freshSalt());
    }

    /// Sell: spend `amountIn` of `other` (currency1 here) for at least `amountOutMin` of the numeraire.
    function _flipSell(PoolKey memory k, address owner, uint256 amountIn, uint256 amountOutMin, uint256 fee)
        internal
        returns (AsyncOrder memory)
    {
        return _order(k, owner, false, amountIn, amountOutMin, fee, _freshSalt());
    }

    function test_numeraireIsConfigured() public view {
        assertEq(Currency.unwrap(hook.numeraire()), Currency.unwrap(usdc));
        assertEq(Currency.unwrap(flipKey.currency0), Currency.unwrap(usdc));
        assertEq(Currency.unwrap(key.currency1), Currency.unwrap(usdc));
    }

    function test_init_requiresNumeraire() public {
        PoolKey memory k = PoolKey(currency0, other, LPFeeLibrary.DYNAMIC_FEE_FLAG, 60, IHooks(address(hook)));
        vm.expectRevert(_wrappedInitError(AsyncSwap.NumeraireRequired.selector));
        manager.initialize(k, SQRT_1_1);
    }

    /// A static fee tier would let one pair open a separate book per tier; only the dynamic-fee flag is admitted.
    function test_init_requiresDynamicFee() public {
        uint24[3] memory tiers = [uint24(500), 3000, 10000];
        for (uint256 i = 0; i < tiers.length; i++) {
            PoolKey memory k = PoolKey(usdc, other, tiers[i], 60, IHooks(address(hook)));
            vm.expectRevert(_wrappedInitError(AsyncSwap.DynamicFeeRequired.selector));
            manager.initialize(k, SQRT_1_1);
        }
    }

    /// A dynamic-fee pool starts with a zero LP fee; a liquidity fill charges LPs 0.30%.
    /// v2 is official on "LP fee restored after pool fills": the 0.30% is charged during the fill (fee growth
    /// accrues) and the slot0 LP fee is back to zero afterwards, instead of staying at 0.30%.
    function test_liquidityFill_setsLpFee() public {
        (,,, uint24 lpFee) = manager.getSlot0(flipKey.toId());
        assertEq(lpFee, 0);
        AsyncOrder memory o = _flipSell(flipKey, maker, 1e15, 1, 0);
        bytes32 id = _place(o);
        assertTrue(_open(flipKey, id), "no liquidity yet: rests");
        _addLiquidity(flipKey);
        (uint256 g0Before, uint256 g1Before) = manager.getFeeGrowthGlobals(flipKey.toId());
        router.fillFromPoolLiquidity(o);
        assertFalse(_open(flipKey, id));
        (uint256 g0After, uint256 g1After) = manager.getFeeGrowthGlobals(flipKey.toId());
        assertTrue(g0After > g0Before || g1After > g1Before, "LPs charged a fee during the fill");
        (,,, lpFee) = manager.getSlot0(flipKey.toId());
        assertEq(lpFee, 0, "LP fee restored after the pool fill");
    }

    /// The numeraire must be a token, never native. Official's constructor also requires code at the address.
    function test_constructor_rejectsNativeNumeraire() public {
        vm.expectRevert(AsyncSwap.InvalidNumeraire.selector);
        new ProofNumeraireConstructorHarness(manager, Currency.wrap(address(0)), protocolOwner);
    }

    /// The side follows the numeraire, not the swap direction: a `zeroForOne` order that spends it is a bid.
    function test_flip_sidesAndPriceKeys() public {
        bytes32 buyId = _place(_flipBuy(flipKey, maker, 2e18, 1e18, 0)); // bid 2
        bytes32 sellId = _place(_flipSell(flipKey, maker2, 1e18, 3e18, 0)); // ask 3

        assertTrue(_isBuyOf(flipKey, buyId), "zeroForOne spending the numeraire is a buy");
        assertFalse(_isBuyOf(flipKey, sellId));
        assertEq(_priceKeyOf(flipKey, buyId), 2e18);
        assertEq(_priceKeyOf(flipKey, sellId), 3e18);

        (bytes32 bestBid, uint128 bidKey) = _best(flipKey, true);
        (bytes32 bestAsk, uint128 askKey) = _best(flipKey, false);
        assertEq(bestBid, buyId);
        assertEq(bestAsk, sellId);
        assertEq(bidKey, 2e18);
        assertEq(askKey, 3e18);
        assertEq(_claims(usdc, address(hook)), 2e18);
        assertEq(_claims(other, address(hook)), 1e18);
    }

    function test_flip_match() public {
        bytes32 sellId = _place(_flipSell(flipKey, maker, 1e18, 2e18, 0)); // ask 2
        uint256 makerUsdc = _bal(usdc, maker);
        uint256 maker2Other = _bal(other, maker2);
        bytes32 buyId = _place(_flipBuy(flipKey, maker2, 2e18, 1e18, 0)); // bid 2: crosses

        assertFalse(_open(flipKey, sellId));
        assertFalse(_open(flipKey, buyId));
        assertEq(_bal(usdc, maker), makerUsdc + 2e18, "seller paid in the numeraire");
        assertEq(_bal(other, maker2), maker2Other + 1e18, "buyer paid in the asset");
        assertEq(_claims(usdc, address(hook)), 0);
        assertEq(_claims(other, address(hook)), 0);
    }

    function test_flip_fill() public {
        AsyncOrder memory o = _flipSell(flipKey, maker, 1e18, 2e18, 0);
        _place(o);
        uint256 fee = _poolFee(2e18);
        uint256 makerUsdc = _bal(usdc, maker);
        uint256 fillerUsdc = _bal(usdc, filler);
        uint256 fillerOther = _bal(other, filler);

        _fill(o, filler);

        assertEq(_bal(usdc, maker), makerUsdc + 2e18);
        assertEq(_bal(usdc, filler), fillerUsdc - 2e18 - fee);
        assertEq(_bal(other, filler), fillerOther + 1e18);
        assertEq(_claims(usdc, address(vault)), fee);
        assertEq(_claims(other, address(hook)), 0);
    }

    /// The bid is pulled, escrowed and donated in the numeraire (currency0), never in the order's input.
    function test_flip_bidInNumeraire() public {
        AsyncOrder memory o = _flipSell(flipPrioKey, maker, 1e18, 2e18, 5e6);
        uint256 makerUsdc = _bal(usdc, maker);
        uint256 makerOther = _bal(other, maker);
        _place(o);
        assertEq(_bal(usdc, maker), makerUsdc - 5e6, "bid paid in the numeraire");
        assertEq(_bal(other, maker), makerOther - 1e18, "only the input leaves in the asset");
        assertEq(_claims(usdc, address(hook)), 5e6);
        assertEq(_claims(other, address(hook)), 1e18);

        _fill(o, filler);
        assertEq(_claims(usdc, address(hook)), 0, "bid left the hook");
        assertEq(_claims(usdc, address(vault)), _poolFee(2e18), "donated, not forfeited");
    }

    /// A partial match donates the matched share of a currency0 bid and keeps the rest escrowed.
    function test_flip_partialMatchDonatesProRata() public {
        bytes32 sellId = _place(_flipSell(flipPrioKey, maker, 2e18, 4e18, 4e6)); // ask 2, bid 4e6
        _place(_flipBuy(flipPrioKey, maker2, 2e18, 1e18, 2e6)); // bid 2: takes half the ask

        assertEq(_amountIn(flipPrioKey, sellId), 1e18);
        assertEq(hook.asyncOrderPriorityFee(flipPrioKey.toId(), sellId), 2e6, "half the seller's bid donated");
        assertEq(_claims(usdc, address(hook)), 2e6, "the seller's remaining bid is the only numeraire claim");
        assertEq(_claims(other, address(hook)), 1e18);
    }
}
