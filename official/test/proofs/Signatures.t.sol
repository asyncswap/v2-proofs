// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {Currency} from "v4-core/types/Currency.sol";
import {PoolIdLibrary, PoolKey} from "v4-core/types/PoolKey.sol";
import {AsyncSwap} from "@async-swap/AsyncSwap.sol";
import {Router} from "@async-swap/Router.sol";
import {AsyncOrder} from "@async-swap/types/AsyncOrder.sol";
import {OrderSignatures} from "@async-swap/libraries/OrderSignatures.sol";
import {ProofBase} from "./ProofBase.sol";

/// @dev Signed actions. Spec: `AsyncSwapSpec/Admin.lean` (`verify_no_replay`, `verify_respects_deadline`,
///      `nonce_monotone`), `Hashing.lean` (witness binding, domain separation),
///      `AsyncSwapProtocol/Model.lean` (`swapWithSig`, `cancelWithSig`, `updatePriceWithSig`).
contract ProofSignaturesTest is ProofBase {
    using PoolIdLibrary for PoolKey;

    address relayer = makeAddr("relayer");

    function test_setExecutorWithSig() public {
        address executor = makeAddr("executor");
        bytes memory sig = _sign(
            makerPk, _hookDigest(OrderSignatures.hashSetExecutor(key, maker, executor, true, 1, block.timestamp + 1))
        );
        vm.prank(relayer);
        hook.setExecutorWithSig(key, maker, executor, true, 1, block.timestamp + 1, sig);
        assertTrue(hook.isExecutor(key.toId(), maker, executor));
        assertTrue(hook.nonceUsed(maker, 1));

        // replay (official errors carry no arguments)
        vm.prank(relayer);
        vm.expectRevert(AsyncSwap.NonceAlreadyUsed.selector);
        hook.setExecutorWithSig(key, maker, executor, true, 1, block.timestamp + 1, sig);

        // wrong signer
        bytes memory bad = _sign(
            maker2Pk, _hookDigest(OrderSignatures.hashSetExecutor(key, maker, executor, true, 2, block.timestamp + 1))
        );
        vm.expectRevert(AsyncSwap.InvalidSignature.selector);
        hook.setExecutorWithSig(key, maker, executor, true, 2, block.timestamp + 1, bad);

        // expired
        bytes memory late = _sign(
            makerPk, _hookDigest(OrderSignatures.hashSetExecutor(key, maker, executor, true, 3, block.timestamp - 1))
        );
        vm.expectRevert(AsyncSwap.SignatureExpired.selector);
        hook.setExecutorWithSig(key, maker, executor, true, 3, block.timestamp - 1, late);
    }

    function test_invalidateNonce() public {
        vm.prank(maker);
        hook.invalidateNonce(9);
        bytes memory sig = _sign(
            makerPk, _hookDigest(OrderSignatures.hashSetExecutor(key, maker, relayer, true, 9, block.timestamp + 1))
        );
        vm.expectRevert(AsyncSwap.NonceAlreadyUsed.selector);
        hook.setExecutorWithSig(key, maker, relayer, true, 9, block.timestamp + 1, sig);
        vm.prank(maker);
        vm.expectRevert(AsyncSwap.NonceAlreadyUsed.selector);
        hook.invalidateNonce(9);
    }

    /// `hashUpdatePrice_inj`: bound to the stored input; a different amount is a different message.
    function test_updatePriceWithSig() public {
        AsyncOrder memory s = _sell(key, maker, 1e18, 2e18, 0);
        bytes32 id = _place(s);
        bytes32 structHash = OrderSignatures.hashUpdatePrice(s, id, 1e18, 3e18, 5, block.timestamp + 1);
        bytes memory sig = _sign(makerPk, _hookDigest(structHash));
        vm.prank(relayer);
        hook.updatePriceWithSig(s, 3e18, 5, block.timestamp + 1, sig);
        assertEq(_amountOutMin(key, id), 3e18);

        // the same signature cannot reprice to something else
        bytes32 other_ = OrderSignatures.hashUpdatePrice(s, id, 1e18, 4e18, 6, block.timestamp + 1);
        bytes memory wrongUse = _sign(makerPk, _hookDigest(other_));
        vm.expectRevert(AsyncSwap.InvalidSignature.selector);
        hook.updatePriceWithSig(s, 5e18, 6, block.timestamp + 1, wrongUse);

        // signed over a different stored input: not valid either
        bytes32 wrongSize = OrderSignatures.hashUpdatePrice(s, id, 2e18, 4e18, 7, block.timestamp + 1);
        bytes memory wrongSizeSig = _sign(makerPk, _hookDigest(wrongSize));
        vm.expectRevert(AsyncSwap.InvalidSignature.selector);
        hook.updatePriceWithSig(s, 4e18, 7, block.timestamp + 1, wrongSizeSig);
    }

    /// `cancelWithSig_requires_sig`, `cancelWithSig_no_replay`, `digest_ne_of_contract` (router domain only).
    function test_cancelWithSig() public {
        AsyncOrder memory s = _sell(key, maker, 1e18, 2e18, 0);
        bytes32 id = _place(s);
        bytes32 structHash = OrderSignatures.hashCancel(s, id, 1e18, 1, block.timestamp + 1);

        // a signature in the hook's domain is not valid for the router
        bytes memory hookDomain = _sign(makerPk, _hookDigest(structHash));
        vm.prank(relayer);
        vm.expectRevert(Router.InvalidSignature.selector);
        router.cancelWithSig(s, 1, block.timestamp + 1, hookDomain);

        // v2's router domain is official: ("AsyncSwap Router", "1") (the rebuild used ("AsyncSwapRouter", "2")).
        bytes32 domain = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256("AsyncSwap Router"),
                keccak256("1"),
                block.chainid,
                address(router)
            )
        );
        assertEq(domain, router.DOMAIN_SEPARATOR());
        bytes32 digest = keccak256(abi.encodePacked("\x19\x01", domain, structHash));
        bytes memory sig = _sign(makerPk, digest);
        uint256 maker0 = _bal(currency0, maker);
        vm.prank(relayer);
        // the failed attempt above burned nothing: the router burns the nonce before checking the signature,
        // and the revert rolled that back.
        router.cancelWithSig(s, 1, block.timestamp + 1, sig);
        // official `cancelWithSig` returns nothing; the refund is observed on the maker's balance.
        assertEq(_bal(currency0, maker), maker0 + 1e18);
        assertTrue(router.cancelNonceUsed(maker, 1));
        assertFalse(_open(key, id));

        // no replay (the order is gone and the nonce is burned)
        vm.prank(relayer);
        vm.expectRevert();
        router.cancelWithSig(s, 1, block.timestamp + 1, sig);
    }

    /// `routerPermit_inj`: the Permit2 message fixes token, amount, spender, nonce, deadline and the order
    /// witness; a relayer cannot substitute any of them. The signed executor grant is applied first.
    function test_swapWithSig_permit2() public {
        AsyncOrder memory s = _sell(key, maker3, 1e18, 2e18, 0);
        s.salt = bytes32(0); // `swapWithSig` always derives the salt (a relayer cannot choose the id)
        vm.prank(maker3);
        hook.setExecutor(key.toId(), address(router), false); // the grant comes with the signature

        uint256 deadline = block.timestamp + 1;
        Router.PermitData memory permit = Router.PermitData(11, deadline, _permitSig(maker3Pk, s, 11, deadline));
        // official `ExecutorGrant` has no `allow` flag: a non-empty signature means "grant".
        Router.ExecutorGrant memory grant = Router.ExecutorGrant(
            12,
            deadline,
            _sign(
                maker3Pk,
                _hookDigest(OrderSignatures.hashSetExecutor(key, maker3, address(router), true, 12, deadline))
            )
        );

        uint256 maker0 = _bal(currency0, maker3);
        vm.recordLogs();
        vm.prank(relayer);
        router.swapWithSig(s, permit, grant);
        (bytes32 id,) = _createdFromLogs(vm.getRecordedLogs());
        assertTrue(_open(key, id));
        assertEq(_bal(currency0, maker3), maker0 - 1e18);
        assertEq(_claims(currency0, address(hook)), 1e18);
        assertTrue(hook.isExecutor(key.toId(), maker3, address(router)));

        // amount substitution fails: the witness and the permitted amount both change
        AsyncOrder memory bigger = _sell(key, maker3, 1e18, 2e18, 0); // a copy: `= s` would alias memory
        bigger.amountIn = 2e18;
        Router.PermitData memory permit2b = Router.PermitData(13, deadline, _permitSig(maker3Pk, s, 13, deadline));
        vm.prank(relayer);
        vm.expectRevert();
        router.swapWithSig(bigger, permit2b, Router.ExecutorGrant(0, 0, ""));

        // salt is not covered by the witness: a second use with a new salt needs a new nonce, not a new signature
        AsyncOrder memory resalted = _sell(key, maker3, 1e18, 2e18, 0);
        resalted.salt = bytes32(uint256(5));
        Router.PermitData memory permitReplay = Router.PermitData(11, deadline, permit.signature);
        vm.prank(relayer);
        vm.expectRevert();
        router.swapWithSig(resalted, permitReplay, Router.ExecutorGrant(0, 0, ""));
    }

    function test_swapWithSig_rejectsNativeInput() public {
        AsyncOrder memory s = _sell(nativeKey, maker, 1 ether, 2e18, 0);
        vm.prank(relayer);
        // official reverts with a require string rather than a custom error
        vm.expectRevert(bytes("Native input needs swap()"));
        router.swapWithSig(s, Router.PermitData(1, block.timestamp + 1, ""), Router.ExecutorGrant(0, 0, ""));
    }
}
