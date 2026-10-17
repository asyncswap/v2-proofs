// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {SetupHook} from "./SetupHook.t.sol";
import {AsyncSwap} from "@async-swap/AsyncSwap.sol";
import {AsyncFiller} from "@async-swap/libraries/AsyncFiller.sol";
import {AsyncOrder} from "@async-swap/types/AsyncOrder.sol";
import {Currency, CurrencyLibrary} from "v4-core/types/Currency.sol";

/// @notice The two improvements the proofs-only rebuild found and the maintainer accepted (decision 9 in
///         asyncswap/v2-proofs README): the priority bid is escrowed in the unlock that creates the order,
///         and the maker may choose the salt so the order id is known before sending.
contract ImprovementsTest is SetupHook {
    using CurrencyLibrary for Currency;

    address alice = makeAddr("alice");

    function setUp() public override {
        super.setUp();
        topUp(alice, 100 ether);
    }

    function _order(bool zeroForOne, uint256 amountIn, uint256 amountOutMin, uint256 bid, bytes32 salt)
        internal
        view
        returns (AsyncOrder memory)
    {
        return AsyncOrder({
            key: key,
            owner: alice,
            zeroForOne: zeroForOne,
            amountIn: amountIn,
            amountOutMin: amountOutMin,
            priorityFee: bid,
            sqrtPrice: 2 ** 96,
            salt: salt
        });
    }

    function _submit(AsyncOrder memory order) internal {
        vm.startPrank(alice);
        token0.approve(address(router), type(uint256).max);
        token1.approve(address(router), type(uint256).max);
        router.swap(
            order,
            abi.encode(
                AsyncSwap.UserParams({
                    user: alice, executor: address(router), amountOutMin: order.amountOutMin, priorityFee: order.priorityFee
                })
            )
        );
        vm.stopPrank();
    }

    /// The maker picks the salt, so the id is computable before the transaction is sent.
    function test_makerSalt_idKnownBeforeSending() public {
        bytes32 salt = keccak256("alice's first order");
        bytes32 id = _orderIdFor(alice, true, salt);
        assertEq(hook.asyncOrder(poolId, id), 0, "slot is free before sending");

        _submit(_order(true, 1 ether, 0.9 ether, 0, salt));

        assertEq(hook.asyncOrder(poolId, id), 1 ether, "the order sits exactly at the id the maker computed");
    }

    /// A zero salt keeps v2's block-data derivation, so every existing integration keeps working.
    function test_zeroSalt_keepsDerivedSalt() public {
        _submit(_order(true, 1 ether, 0.9 ether, 0, bytes32(0)));

        bytes32 id = _orderIdFor(alice, true, _expectedSalt(alice, 1 ether, 0.9 ether));
        assertEq(hook.asyncOrder(poolId, id), 1 ether);
    }

    /// Reusing a salt cannot overwrite an open order: the hook walks `salt = keccak256(salt)`.
    function test_reusedMakerSalt_walksToAFreeId() public {
        bytes32 salt = keccak256("reused");
        _submit(_order(true, 1 ether, 0.9 ether, 0, salt));
        _submit(_order(true, 2 ether, 1.8 ether, 0, salt));

        assertEq(hook.asyncOrder(poolId, _orderIdFor(alice, true, salt)), 1 ether, "first order untouched");
        bytes32 walked = keccak256(abi.encode(salt));
        assertEq(hook.asyncOrder(poolId, _orderIdFor(alice, true, walked)), 2 ether, "second order at the walked id");
    }

    /// The bid becomes the hook's claim in the same unlock that creates the order; there is no
    /// separate record step and no escrowed flag to check later.
    function test_bidEscrowedInCreateUnlock() public {
        hook.setOrderingMode(key, AsyncFiller.OrderingMode.PriorityFee);
        uint256 bid = 100_000;
        bytes32 salt = keccak256("bid");
        uint256 hookUsdcBefore = manager.balanceOf(address(hook), currency1.toId());
        uint256 aliceUsdcBefore = token1.balanceOf(alice);

        // Input is currency0, so every currency1 (numeraire) claim the hook gains is the bid.
        _submit(_order(true, 1 ether, 0.9 ether, bid, salt));

        bytes32 id = _orderIdFor(alice, true, salt);
        assertEq(hook.asyncOrderPriorityFee(poolId, id), bid, "bid recorded on the order");
        assertEq(manager.balanceOf(address(hook), currency1.toId()) - hookUsdcBefore, bid, "bid held as a hook claim");
        assertEq(aliceUsdcBefore - token1.balanceOf(alice), bid, "maker paid exactly the bid");
    }

    /// The old two-step path is gone from the ABI.
    function test_noRecordPriorityFeeStep() public {
        (bool ok,) = address(hook).call(
            abi.encodeWithSignature(
                "recordPriorityFee((address,address,uint24,int24,address),address,uint256)", key, alice, 1
            )
        );
        assertFalse(ok, "recordPriorityFee no longer exists");
    }
}
