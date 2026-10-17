// SPDX-License-Identifier: MIT
pragma solidity 0.8.26;

import {Test} from "forge-std/Test.sol";
import {StdInvariant} from "forge-std/StdInvariant.sol";
import {AsyncSwap} from "src/AsyncSwap.sol";
import {NativeClaims} from "src/NativeClaims.sol";
import {Router} from "src/Router.sol";
import {AsyncOrder} from "src/types/AsyncOrder.sol";
import {AsyncFiller} from "src/libraries/AsyncFiller.sol";
import {ISignatureTransfer} from "src/interfaces/ISignatureTransfer.sol";
import {MockERC20} from "./utils/MockERC20.sol";
import {PoolManager} from "v4-core/PoolManager.sol";
import {Hooks} from "v4-core/libraries/Hooks.sol";
import {LPFeeLibrary} from "v4-core/libraries/LPFeeLibrary.sol";
import {Currency} from "v4-core/types/Currency.sol";
import {PoolIdLibrary, PoolKey} from "v4-core/types/PoolKey.sol";

contract MatchingHandler is Test {
    using PoolIdLibrary for PoolKey;
    AsyncSwap public hook;
    Router public router;
    NativeClaims public claims;
    MockERC20 public usdc;
    PoolKey public key;
    address[4] public actors;
    AsyncOrder[] internal orders;
    bool public priority;
    uint256 public submissions;
    uint256 public cancellations;
    uint256 public updates;

    constructor(AsyncSwap h, Router r, MockERC20 u, PoolKey memory k, bool p) {
        hook = h;
        router = r;
        claims = new NativeClaims(h.poolManager());
        usdc = u;
        key = k;
        priority = p;
        for (uint256 i; i < 4; ++i) {
            address actor = address(uint160(0xC000 + i));
            actors[i] = actor;
            vm.deal(actor, 1_000 ether);
            u.mint(actor, 10_000_000e6);
            vm.startPrank(actor);
            u.approve(address(r), type(uint256).max);
            h.setExecutor(k.toId(), address(r), true);
            vm.stopPrank();
        }
    }

    function submit(uint256 who, bool sell, uint256 size, uint256 price, uint256 fee) external {
        address actor = actors[who % 4];
        uint256 quantity = bound(size, 1e12, 1 ether);
        uint256 quote = quantity * bound(price, 1_000e6, 4_000e6) / 1 ether;
        uint256 bid = priority ? bound(fee, 100_000, 10e6) : 0;
        uint256 amount = sell ? quantity : quote;
        uint256 minimum = sell ? quote : quantity;
        vm.roll(block.number + 1); // unique salt, including repeated actor/amount combinations
        AsyncOrder memory order = AsyncOrder(key, actor, sell, amount, minimum, bid, 2 ** 96, bytes32(0));
        vm.prank(actor);
        router.swap{value: sell ? amount : 0}(
            order, abi.encode(AsyncSwap.UserParams(actor, address(router), minimum, bid))
        );
        order.salt = keccak256(
            abi.encode(block.timestamp, block.number, address(hook.poolManager()), actor, amount, minimum, bid)
        );
        orders.push(order);
        ++submissions;
    }

    function cancel(uint256 index) external {
        if (orders.length == 0) return;
        AsyncOrder memory order = orders[index % orders.length];
        if (hook.asyncOrder(key.toId(), id(order)) == 0) return;
        vm.prank(order.owner);
        router.cancelOrder(order);
        ++cancellations;
    }

    function reprice(uint256 index, uint256 price) external {
        if (orders.length == 0) return;
        AsyncOrder memory order = orders[index % orders.length];
        uint256 remaining = hook.asyncOrder(key.toId(), id(order));
        if (remaining == 0) return;
        uint256 p = bound(price, 1_000e6, 4_000e6);
        uint256 minimum = order.zeroForOne ? remaining * p / 1 ether : remaining * 1 ether / p;
        if (minimum == 0) return;
        vm.prank(order.owner);
        hook.updatePrice(order, minimum);
        ++updates;
    }

    function redeem(uint256 who, uint256 size) external {
        address actor = actors[who % 4];
        uint256 balance = hook.poolManager().balanceOf(actor, 0);
        if (balance == 0) return;
        uint256 amount = bound(size, 1, balance);
        vm.startPrank(actor);
        hook.poolManager().approve(address(claims), 0, amount);
        claims.redeem(actor, amount);
        vm.stopPrank();
    }

    function clear(uint8 count) external {
        router.matchBook(key, uint8(bound(count, 1, 8)));
    }

    function id(AsyncOrder memory order) public view returns (bytes32) {
        return keccak256(abi.encode(block.chainid, key.toId(), order.owner, order.zeroForOne, order.salt));
    }

    function orderCount() external view returns (uint256) {
        return orders.length;
    }

    function orderAt(uint256 index) external view returns (AsyncOrder memory) {
        return orders[index];
    }
}

contract MatchingInvariantTest is StdInvariant, Test {
    using PoolIdLibrary for PoolKey;
    PoolManager manager;
    AsyncSwap hook;
    MockERC20 usdc;
    MatchingHandler handler;
    PoolKey key;

    function priorityMode() internal pure virtual returns (bool) {
        return false;
    }

    function setUp() public {
        manager = new PoolManager(address(this));
        usdc = new MockERC20("USD Coin", "USDC", 6);
        uint160 flags = uint160(
            Hooks.BEFORE_INITIALIZE_FLAG | Hooks.BEFORE_SWAP_FLAG | Hooks.BEFORE_ADD_LIQUIDITY_FLAG
                | Hooks.BEFORE_SWAP_RETURNS_DELTA_FLAG
        );
        deployCodeTo("AsyncSwap.sol", abi.encode(manager, Currency.wrap(address(usdc)), address(this)), address(flags));
        hook = AsyncSwap(payable(address(flags)));
        Router router = new Router(manager, hook, ISignatureTransfer(address(0)));
        key = PoolKey(Currency.wrap(address(0)), Currency.wrap(address(usdc)), LPFeeLibrary.DYNAMIC_FEE_FLAG, 1, hook);
        manager.initialize(key, 2 ** 96);
        if (priorityMode()) hook.setOrderingMode(key, AsyncFiller.OrderingMode.PriorityFee);
        handler = new MatchingHandler(hook, router, usdc, key, priorityMode());
        bytes4[] memory selectors = new bytes4[](5);
        selectors[0] = MatchingHandler.submit.selector;
        selectors[1] = MatchingHandler.cancel.selector;
        selectors[2] = MatchingHandler.reprice.selector;
        selectors[3] = MatchingHandler.clear.selector;
        selectors[4] = MatchingHandler.redeem.selector;
        targetSelector(FuzzSelector(address(handler), selectors));
        targetContract(address(handler));
    }

    function invariant_escrowEqualsOutstandingObligations() public view {
        uint256 ethOwed;
        uint256 usdcOwed;
        uint256 count = handler.orderCount();
        for (uint256 i; i < count; ++i) {
            AsyncOrder memory order = handler.orderAt(i);
            bytes32 orderId = handler.id(order);
            uint256 remaining = hook.asyncOrder(key.toId(), orderId);
            if (order.zeroForOne) ethOwed += remaining;
            else usdcOwed += remaining;
            usdcOwed += hook.asyncOrderPriorityFee(key.toId(), orderId);
        }
        assertEq(manager.balanceOf(address(hook), 0), ethOwed, "native escrow obligations");
        assertEq(manager.balanceOf(address(hook), uint160(address(usdc))), usdcOwed, "USDC escrow obligations");
    }

    function invariant_assetsConserved() public view {
        uint256 ethTotal = address(manager).balance;
        uint256 usdcTotal = usdc.balanceOf(address(manager));
        for (uint256 i; i < 4; ++i) {
            address actor = handler.actors(i);
            ethTotal += actor.balance;
            usdcTotal += usdc.balanceOf(actor);
        }
        uint256 nativeClaims = manager.balanceOf(address(hook), 0) + manager.balanceOf(address(hook.feeVault()), 0);
        for (uint256 i; i < 4; ++i) {
            nativeClaims += manager.balanceOf(handler.actors(i), 0);
        }
        assertEq(address(manager).balance, nativeClaims, "all native claims backed exactly");
        assertEq(ethTotal, 4_000 ether);
        assertEq(usdcTotal, 40_000_000e6);
    }

    function invariant_bestPricesAgreeWithLinearScan() public view {
        uint128 bestBid;
        uint128 bestAsk = type(uint128).max;
        bool hasBid;
        bool hasAsk;
        for (uint256 i; i < handler.orderCount(); ++i) {
            AsyncOrder memory order = handler.orderAt(i);
            (, uint256 amount,, uint128 price, bool buy,,) = hook.orderBookOrder(key.toId(), handler.id(order));
            if (amount == 0) continue;
            if (buy) {
                hasBid = true;
                if (price > bestBid) bestBid = price;
            } else {
                hasAsk = true;
                if (price < bestAsk) bestAsk = price;
            }
        }
        (bool bidFound, uint128 bid,,) = hook.bestOrder(key.toId(), true);
        (bool askFound, uint128 ask,,) = hook.bestOrder(key.toId(), false);
        assertEq(bidFound, hasBid);
        assertEq(askFound, hasAsk);
        if (hasBid) assertEq(bid, bestBid);
        if (hasAsk) assertEq(ask, bestAsk);
    }
}

contract PriorityMatchingInvariantTest is MatchingInvariantTest {
    function priorityMode() internal pure override returns (bool) {
        return true;
    }
}
