// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {Test} from "forge-std/Test.sol";
import {Currency} from "v4-core/types/Currency.sol";
import {PoolKey} from "v4-core/types/PoolKey.sol";
import {IHooks} from "v4-core/interfaces/IHooks.sol";
import {OrderSignatures} from "@async-swap/libraries/OrderSignatures.sol";
import {AsyncOrder} from "@async-swap/types/AsyncOrder.sol";
import {OrderIdHarness} from "./ProofBase.sol";

/// @dev Spec: `AsyncSwapSpec/Hashing.lean` — the type strings and what each hash binds.
contract ProofOrderSignaturesTest is Test {
    PoolKey k = PoolKey(Currency.wrap(address(1)), Currency.wrap(address(2)), 3000, 60, IHooks(address(0x88)));
    OrderIdHarness ids;

    function setUp() public {
        ids = new OrderIdHarness();
    }

    function _o() internal view returns (AsyncOrder memory) {
        return AsyncOrder(k, address(0xA), true, 1e18, 2e18, 5, 12345, bytes32(uint256(7)));
    }

    /// Official exposes the type strings as library constants rather than getters; v2's strings are official.
    function test_typeStringsMatchSpec() public pure {
        assertEq(
            keccak256(bytes(OrderSignatures.PERMIT2_WITNESS_TYPE)),
            keccak256(
                "AsyncOrder witness)AsyncOrder(address maker,address tokenIn,address tokenOut,uint256 amountIn,uint256 amountOutMin,uint256 priorityFee,PoolKey pool)PoolKey(address currency0,address currency1,uint24 fee,int24 tickSpacing,address hooks)TokenPermissions(address token,uint256 amount)"
            )
        );
        assertEq(
            OrderSignatures.ASYNC_ORDER_TYPEHASH,
            keccak256(
                "AsyncOrder(address maker,address tokenIn,address tokenOut,uint256 amountIn,uint256 amountOutMin,uint256 priorityFee,PoolKey pool)PoolKey(address currency0,address currency1,uint24 fee,int24 tickSpacing,address hooks)"
            )
        );
        assertEq(
            OrderSignatures.SET_EXECUTOR_TYPEHASH,
            keccak256(
                "SetExecutor(address maker,address executor,bool allow,PoolKey pool,uint256 nonce,uint256 deadline)PoolKey(address currency0,address currency1,uint24 fee,int24 tickSpacing,address hooks)"
            )
        );
    }

    /// `hashOrder_inj`: the witness binds maker, tokens, amounts, bid and pool — not `sqrtPrice` nor `salt`.
    function test_witnessBinding() public view {
        AsyncOrder memory a = _o();
        AsyncOrder memory b = _o();
        b.sqrtPrice = 999;
        b.salt = bytes32(uint256(8));
        assertEq(OrderSignatures.hashOrder(a), OrderSignatures.hashOrder(b), "sqrtPrice and salt not covered");

        AsyncOrder memory c = _o();
        c.amountIn = 1e18 + 1;
        assertNotEq(OrderSignatures.hashOrder(a), OrderSignatures.hashOrder(c));
        c = _o();
        c.priorityFee = 6;
        assertNotEq(OrderSignatures.hashOrder(a), OrderSignatures.hashOrder(c));
        c = _o();
        c.zeroForOne = false;
        assertNotEq(OrderSignatures.hashOrder(a), OrderSignatures.hashOrder(c), "direction via tokens");
        c = _o();
        c.key.fee = 500;
        assertNotEq(OrderSignatures.hashOrder(a), OrderSignatures.hashOrder(c), "pool");
    }

    /// `orderId_inj`: an id fixes chain, pool, maker, direction and salt — not the amounts.
    function test_orderIdBinding() public view {
        AsyncOrder memory a = _o();
        AsyncOrder memory b = _o();
        b.amountIn = 5;
        b.amountOutMin = 6;
        b.priorityFee = 0;
        assertEq(ids.orderId(a), ids.orderId(b));
        b = _o();
        b.salt = bytes32(uint256(8));
        assertNotEq(ids.orderId(a), ids.orderId(b));
        b = _o();
        b.zeroForOne = false;
        assertNotEq(ids.orderId(a), ids.orderId(b));
    }

    /// Type separation: no struct hash of one type equals one of another.
    function test_typeSeparation() public view {
        AsyncOrder memory o = _o();
        bytes32 id = ids.orderId(o);
        bytes32 h1 = OrderSignatures.hashOrder(o);
        bytes32 h2 = OrderSignatures.hashSetExecutor(k, o.owner, address(0xB), true, 1, 2);
        // Official signatures: hashUpdatePrice / hashCancel take the order (tokens from its direction).
        bytes32 h3 = OrderSignatures.hashUpdatePrice(o, id, 1e18, 3e18, 1, 2);
        bytes32 h4 = OrderSignatures.hashCancel(o, id, 1e18, 1, 2);
        bytes32 h5 = OrderSignatures.hashPoolKey(k);
        assertTrue(h1 != h2 && h1 != h3 && h1 != h4 && h1 != h5 && h2 != h3 && h2 != h4 && h3 != h4);
    }
}
