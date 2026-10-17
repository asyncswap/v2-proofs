// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Deployers} from "v4-core-test/utils/Deployers.sol";
import {MockERC20} from "solmate/src/test/utils/mocks/MockERC20.sol";
import {Hooks} from "v4-core/libraries/Hooks.sol";
import {IHooks} from "v4-core/interfaces/IHooks.sol";
import {IPoolManager} from "v4-core/interfaces/IPoolManager.sol";
import {Currency, CurrencyLibrary} from "v4-core/types/Currency.sol";
import {PoolKey} from "v4-core/types/PoolKey.sol";
import {PoolId} from "v4-core/types/PoolId.sol";
import {Constants} from "v4-core-test/utils/Constants.sol";

import {AsyncSwap} from "../../src/AsyncSwap.sol";
import {Router} from "../../src/Router.sol";
import {FeeVault} from "../../src/FeeVault.sol";
import {NativeClaims} from "../../src/NativeClaims.sol";
import {AsyncOrder, AsyncOrderLibrary} from "../../src/types/AsyncOrder.sol";
import {AsyncFiller} from "../../src/libraries/AsyncFiller.sol";
import {ProtocolFee} from "../../src/libraries/ProtocolFee.sol";
import {MockPermit2} from "./MockPermit2.sol";

/// @notice Shared deployment: PoolManager, two ERC-20s, the hook at a flagged address, Router, FeeVault,
///         NativeClaims, a mock Permit2, and four pools:
///         `key` (FIFO, liquidity), `prioKey` (PriorityFee, liquidity), `emptyKey` (PriorityFee, no liquidity),
///         `nativeKey` (FIFO, native currency0, liquidity).
contract BaseTest is Deployers {
    using AsyncOrderLibrary for AsyncOrder;
    using CurrencyLibrary for Currency;

    AsyncSwap hook;
    Router router;
    FeeVault vault;
    NativeClaims nativeClaims;
    MockPermit2 permit2;

    PoolKey prioKey;
    PoolKey emptyKey;
    // `nativeKey` is declared by Deployers.

    address protocolOwner = makeAddr("protocolOwner");
    address maker;
    uint256 makerPk;
    address maker2;
    uint256 maker2Pk;
    address maker3;
    uint256 maker3Pk;
    address filler = makeAddr("filler");
    address keeper = makeAddr("keeper");

    uint256 constant FUND = 1_000_000 ether;

    function setUp() public virtual {
        (maker, makerPk) = makeAddrAndKey("maker");
        (maker2, maker2Pk) = makeAddrAndKey("maker2");
        (maker3, maker3Pk) = makeAddrAndKey("maker3");

        deployFreshManagerAndRouters();
        deployMintAndApprove2Currencies();

        vault = new FeeVault(manager, protocolOwner);
        address hookAddress = address(
            uint160(
                (uint256(keccak256("AsyncSwap hook")) & ~uint256(Hooks.ALL_HOOK_MASK)) | Hooks.BEFORE_SWAP_FLAG
                    | Hooks.BEFORE_SWAP_RETURNS_DELTA_FLAG
            )
        );
        deployCodeTo("AsyncSwap.sol:AsyncSwap", abi.encode(manager, address(vault), protocolOwner), hookAddress);
        hook = AsyncSwap(payable(hookAddress));
        permit2 = new MockPermit2();
        router = new Router(manager, hook, permit2);
        nativeClaims = new NativeClaims(manager);

        (key,) = initPool(currency0, currency1, IHooks(hook), 3000, 60, Constants.SQRT_PRICE_1_1);
        modifyLiquidityRouter.modifyLiquidity(key, LIQUIDITY_PARAMS, ZERO_BYTES);
        (prioKey,) = initPool(currency0, currency1, IHooks(hook), 500, 60, Constants.SQRT_PRICE_1_1);
        modifyLiquidityRouter.modifyLiquidity(prioKey, LIQUIDITY_PARAMS, ZERO_BYTES);
        (emptyKey,) = initPool(currency0, currency1, IHooks(hook), 10000, 60, Constants.SQRT_PRICE_1_1);
        vm.deal(address(this), 100 ether);
        (nativeKey,) =
            initPool(CurrencyLibrary.ADDRESS_ZERO, currency1, IHooks(hook), 3000, 60, Constants.SQRT_PRICE_1_1);
        modifyLiquidityRouter.modifyLiquidity{value: 10 ether}(nativeKey, LIQUIDITY_PARAMS, ZERO_BYTES);

        vm.startPrank(protocolOwner);
        hook.setOrderingMode(prioKey, AsyncFiller.OrderingMode.PriorityFee);
        hook.setOrderingMode(emptyKey, AsyncFiller.OrderingMode.PriorityFee);
        vm.stopPrank();

        address[5] memory users = [maker, maker2, maker3, filler, keeper];
        for (uint256 i = 0; i < users.length; i++) {
            _fund(users[i]);
            _grantRouter(users[i]);
        }
    }

    /* ─────────────────────────────────── helpers ─────────────────────────────────── */

    function _fund(address who) internal {
        MockERC20(Currency.unwrap(currency0)).transfer(who, FUND);
        MockERC20(Currency.unwrap(currency1)).transfer(who, FUND);
        vm.deal(who, 1000 ether);
        vm.startPrank(who);
        MockERC20(Currency.unwrap(currency0)).approve(address(router), type(uint256).max);
        MockERC20(Currency.unwrap(currency1)).approve(address(router), type(uint256).max);
        MockERC20(Currency.unwrap(currency0)).approve(address(permit2), type(uint256).max);
        MockERC20(Currency.unwrap(currency1)).approve(address(permit2), type(uint256).max);
        vm.stopPrank();
    }

    function _grantRouter(address who) internal {
        vm.startPrank(who);
        hook.setExecutor(key, address(router), true);
        hook.setExecutor(prioKey, address(router), true);
        hook.setExecutor(emptyKey, address(router), true);
        hook.setExecutor(nativeKey, address(router), true);
        vm.stopPrank();
    }

    function _order(
        PoolKey memory k,
        address owner,
        bool zeroForOne,
        uint256 amountIn,
        uint256 amountOutMin,
        uint256 priorityFee,
        bytes32 salt
    ) internal pure returns (AsyncOrder memory) {
        return AsyncOrder(k, owner, zeroForOne, amountIn, amountOutMin, priorityFee, 0, salt);
    }

    /// @dev Sell `amountIn` of currency0 for at least `amountOutMin` of currency1.
    function _sell(PoolKey memory k, address owner, uint256 amountIn, uint256 amountOutMin, uint256 fee)
        internal
        view
        returns (AsyncOrder memory)
    {
        return _order(k, owner, true, amountIn, amountOutMin, fee, bytes32(uint256(vm.getNonce(owner) + 1)));
    }

    /// @dev Buy: spend `amountIn` of currency1 for at least `amountOutMin` of currency0.
    function _buy(PoolKey memory k, address owner, uint256 amountIn, uint256 amountOutMin, uint256 fee)
        internal
        view
        returns (AsyncOrder memory)
    {
        return _order(k, owner, false, amountIn, amountOutMin, fee, bytes32(uint256(vm.getNonce(owner) + 1)));
    }

    function _place(AsyncOrder memory o) internal returns (bytes32 id) {
        uint256 value = o.input().isAddressZero() ? o.amountIn : 0;
        vm.prank(o.owner);
        id = router.swap{value: value}(o);
    }

    function _fill(AsyncOrder memory o, address who)
        internal
        returns (uint256 amountIn, uint256 amountOut, uint256 fee)
    {
        AsyncFiller.OrderInfo memory info = hook.getOrder(o.key, o.orderId());
        uint256 live = ProtocolFee.gross(info.amountOutMin);
        uint256 value = o.output().isAddressZero() ? live : 0;
        vm.prank(who);
        return router.fillOrder{value: value}(o, live);
    }

    function _claims(Currency c, address who) internal view returns (uint256) {
        return manager.balanceOf(who, c.toId());
    }

    function _bal(Currency c, address who) internal view returns (uint256) {
        return c.balanceOf(who);
    }

    function _open(PoolKey memory k, bytes32 id) internal view returns (bool) {
        return hook.getOrder(k, id).amountIn != 0;
    }

    /// @dev `escrowOf` summed over `ids` (`V2/Invariants.lean` `owed`), for the hook's claims in `c`.
    function _owed(PoolKey memory k, bytes32[] memory ids, Currency c) internal view returns (uint256 total) {
        for (uint256 i = 0; i < ids.length; i++) {
            AsyncFiller.OrderInfo memory info = hook.getOrder(k, ids[i]);
            if (info.amountIn == 0) continue;
            Currency input = info.zeroForOne ? k.currency0 : k.currency1;
            if (input == c) total += info.amountIn;
            if (c == k.currency1) total += info.priorityFee;
        }
    }

    function _sign(uint256 pk, bytes32 digest) internal pure returns (bytes memory) {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(pk, digest);
        return abi.encodePacked(r, s, v);
    }

    function _hookDigest(bytes32 structHash) internal view returns (bytes32) {
        return keccak256(abi.encodePacked("\x19\x01", hook.DOMAIN_SEPARATOR(), structHash));
    }
}
