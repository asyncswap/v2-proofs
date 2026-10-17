// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {Test, Vm} from "forge-std/Test.sol";
import {AsyncSwap} from "@async-swap/AsyncSwap.sol";
import {Router} from "@async-swap/Router.sol";
import {FeeVault} from "@async-swap/FeeVault.sol";
import {NativeClaims} from "@async-swap/NativeClaims.sol";
import {AsyncFiller} from "@async-swap/libraries/AsyncFiller.sol";
import {OrderSignatures} from "@async-swap/libraries/OrderSignatures.sol";
import {AsyncOrder} from "@async-swap/types/AsyncOrder.sol";
import {ISignatureTransfer} from "@async-swap/interfaces/ISignatureTransfer.sol";
import {MockERC20} from "../utils/MockERC20.sol";
import {Permit2Bytecode} from "../utils/Permit2Bytecode.sol";
import {PoolManager} from "v4-core/PoolManager.sol";
import {IPoolManager} from "v4-core/interfaces/IPoolManager.sol";
import {IHooks} from "v4-core/interfaces/IHooks.sol";
import {Hooks} from "v4-core/libraries/Hooks.sol";
import {LPFeeLibrary} from "v4-core/libraries/LPFeeLibrary.sol";
import {PoolModifyLiquidityTest} from "v4-core/test/PoolModifyLiquidityTest.sol";
import {ModifyLiquidityParams} from "v4-core/types/PoolOperation.sol";
import {Currency, CurrencyLibrary} from "v4-core/types/Currency.sol";
import {PoolId} from "v4-core/types/PoolId.sol";
import {PoolIdLibrary, PoolKey} from "v4-core/types/PoolKey.sol";
import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";

interface IPermit2Domain {
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}

/// @notice Exposes `AsyncOrderLibrary.orderId`, which only takes calldata.
contract OrderIdHarness {
    function orderId(AsyncOrder calldata order) external view returns (bytes32) {
        return order.orderId();
    }
}

/// @notice The proofs-only rebuild's `BaseTest`, re-expressed on the official deployment: PoolManager, the
///         AsyncSwap hook at its flag address, Router with the real Permit2 bytecode, NativeClaims, three
///         ERC-20s and seven pools. The numeraire (`usdc`) is currency1 in `key` (FIFO, no liquidity),
///         `liqKey` (FIFO, liquidity), `prioKey` (PriorityFee, liquidity), `emptyKey` (PriorityFee, no
///         liquidity) and `nativeKey` (FIFO, native currency0, no liquidity); it is currency0 in `flipKey`
///         (FIFO, no liquidity), `flipLiqKey` (FIFO, liquidity) and `flipPrioKey` (PriorityFee, liquidity).
/// @dev    Official v2 retries every resting remainder against pool liquidity right after matching
///         ("pool fallback after matching"), so the pools whose orders must rest are liquidity-free.
contract ProofBase is Test {
    using PoolIdLibrary for PoolKey;
    using CurrencyLibrary for Currency;

    uint160 constant SQRT_1_1 = 2 ** 96;
    uint256 constant FUND = 1_000_000 ether;
    bytes32 constant TOKEN_PERMISSIONS_TYPEHASH = keccak256("TokenPermissions(address token,uint256 amount)");

    IPoolManager manager;
    AsyncSwap hook;
    Router router;
    FeeVault vault;
    NativeClaims nativeClaims;
    PoolModifyLiquidityTest lpRouter;
    OrderIdHarness idHarness;

    Currency currency0; // the asset in (asset, usdc) pools
    Currency currency1; // == usdc
    Currency usdc;
    Currency other; // sorts above usdc

    PoolKey key;
    PoolKey liqKey;
    PoolKey prioKey;
    PoolKey emptyKey;
    PoolKey nativeKey;
    PoolKey flipKey;
    PoolKey flipLiqKey;
    PoolKey flipPrioKey;

    address protocolOwner = makeAddr("protocolOwner");
    address maker;
    uint256 makerPk;
    address maker2;
    uint256 maker2Pk;
    address maker3;
    uint256 maker3Pk;
    address filler = makeAddr("filler");
    address keeper = makeAddr("keeper");

    function setUp() public virtual {
        (maker, makerPk) = makeAddrAndKey("maker");
        (maker2, maker2Pk) = makeAddrAndKey("maker2");
        (maker3, maker3Pk) = makeAddrAndKey("maker3");

        manager = new PoolManager(address(this));
        address[3] memory t;
        for (uint256 i; i < 3; ++i) {
            t[i] = address(new MockERC20("T", "T", 18));
        }
        // sort ascending: t[0] < t[1] < t[2]
        for (uint256 i; i < 3; ++i) {
            for (uint256 j = i + 1; j < 3; ++j) {
                if (t[j] < t[i]) (t[i], t[j]) = (t[j], t[i]);
            }
        }
        currency0 = Currency.wrap(t[0]);
        usdc = Currency.wrap(t[1]);
        currency1 = usdc;
        other = Currency.wrap(t[2]);
        vm.label(t[0], "asset");
        vm.label(t[1], "usdc");
        vm.label(t[2], "other");

        uint160 flags = uint160(
            Hooks.BEFORE_INITIALIZE_FLAG | Hooks.BEFORE_SWAP_FLAG | Hooks.BEFORE_ADD_LIQUIDITY_FLAG
                | Hooks.BEFORE_SWAP_RETURNS_DELTA_FLAG
        );
        deployCodeTo("AsyncSwap.sol", abi.encode(manager, usdc, protocolOwner), address(flags));
        hook = AsyncSwap(payable(address(flags)));
        vault = hook.feeVault();
        vm.etch(Permit2Bytecode.PERMIT2, Permit2Bytecode.RUNTIME);
        router = new Router(manager, hook, ISignatureTransfer(Permit2Bytecode.PERMIT2));
        nativeClaims = new NativeClaims(manager);
        lpRouter = new PoolModifyLiquidityTest(manager);
        idHarness = new OrderIdHarness();

        key = _init(currency0, usdc, 60);
        liqKey = _init(currency0, usdc, 30);
        prioKey = _init(currency0, usdc, 10);
        emptyKey = _init(currency0, usdc, 20);
        nativeKey = _init(CurrencyLibrary.ADDRESS_ZERO, usdc, 60);
        flipKey = _init(usdc, other, 60);
        flipLiqKey = _init(usdc, other, 30);
        flipPrioKey = _init(usdc, other, 10);

        vm.startPrank(protocolOwner);
        hook.setOrderingMode(prioKey, AsyncFiller.OrderingMode.PriorityFee);
        hook.setOrderingMode(emptyKey, AsyncFiller.OrderingMode.PriorityFee);
        hook.setOrderingMode(flipPrioKey, AsyncFiller.OrderingMode.PriorityFee);
        vm.stopPrank();

        _addLiquidity(liqKey);
        _addLiquidity(prioKey);
        _addLiquidity(flipLiqKey);
        _addLiquidity(flipPrioKey);

        address[5] memory users = [maker, maker2, maker3, filler, keeper];
        for (uint256 i = 0; i < users.length; i++) {
            _fund(users[i]);
            _grantRouter(users[i]);
        }
    }

    /* ─────────────────────────────────── setup helpers ─────────────────────────────────── */

    function _init(Currency a, Currency b, int24 tickSpacing) internal returns (PoolKey memory k) {
        k = PoolKey(a, b, LPFeeLibrary.DYNAMIC_FEE_FLAG, tickSpacing, IHooks(address(hook)));
        manager.initialize(k, SQRT_1_1);
    }

    /// @dev Same position as the rebuild's `LIQUIDITY_PARAMS`: ±120 ticks, 1e18 liquidity.
    function _addLiquidity(PoolKey memory k) internal {
        Currency[3] memory tokens = [currency0, usdc, other];
        for (uint256 i; i < 3; ++i) {
            MockERC20 token = MockERC20(Currency.unwrap(tokens[i]));
            token.mint(address(this), 1_000 ether);
            token.approve(address(lpRouter), type(uint256).max);
        }
        uint256 value = k.currency0.isAddressZero() ? 10 ether : 0;
        if (value != 0) vm.deal(address(this), address(this).balance + value);
        lpRouter.modifyLiquidity{value: value}(
            k, ModifyLiquidityParams({tickLower: -120, tickUpper: 120, liquidityDelta: 1e18, salt: bytes32(0)}), ""
        );
    }

    function _fund(address who) internal {
        Currency[3] memory tokens = [currency0, usdc, other];
        vm.deal(who, 1000 ether);
        for (uint256 i = 0; i < tokens.length; i++) {
            MockERC20 token = MockERC20(Currency.unwrap(tokens[i]));
            token.mint(who, FUND);
            vm.startPrank(who);
            token.approve(address(router), type(uint256).max);
            token.approve(Permit2Bytecode.PERMIT2, type(uint256).max);
            vm.stopPrank();
        }
    }

    function _grantRouter(address who) internal {
        PoolKey[8] memory ks = [key, liqKey, prioKey, emptyKey, nativeKey, flipKey, flipLiqKey, flipPrioKey];
        vm.startPrank(who);
        for (uint256 i; i < ks.length; ++i) {
            hook.setExecutor(ks[i].toId(), address(router), true);
        }
        vm.stopPrank();
    }

    /* ─────────────────────────────────── order helpers ─────────────────────────────────── */

    function _order(
        PoolKey memory k,
        address owner,
        bool zeroForOne,
        uint256 amountIn,
        uint256 amountOutMin,
        uint256 fee,
        bytes32 salt
    ) internal pure returns (AsyncOrder memory) {
        return AsyncOrder(k, owner, zeroForOne, amountIn, amountOutMin, fee, SQRT_1_1, salt);
    }

    uint256 internal saltCounter;

    function _freshSalt() internal returns (bytes32) {
        return keccak256(abi.encode("proof salt", ++saltCounter));
    }

    /// @dev Sell `amountIn` of currency0 for at least `amountOutMin` of currency1, with a maker-chosen salt.
    function _sell(PoolKey memory k, address owner, uint256 amountIn, uint256 amountOutMin, uint256 fee)
        internal
        returns (AsyncOrder memory)
    {
        return _order(k, owner, true, amountIn, amountOutMin, fee, _freshSalt());
    }

    /// @dev Buy: spend `amountIn` of currency1 for at least `amountOutMin` of currency0.
    function _buy(PoolKey memory k, address owner, uint256 amountIn, uint256 amountOutMin, uint256 fee)
        internal
        returns (AsyncOrder memory)
    {
        return _order(k, owner, false, amountIn, amountOutMin, fee, _freshSalt());
    }

    function _userData(AsyncOrder memory o) internal view returns (bytes memory) {
        return abi.encode(AsyncSwap.UserParams(o.owner, address(router), o.amountOutMin, o.priorityFee));
    }

    /// @dev Submit through `Router.swap`. Writes the final (possibly walked) salt back into `o` and returns
    ///      the id, both read from `AsyncOrderCreated` (the official `swap` returns nothing).
    function _place(AsyncOrder memory o) internal returns (bytes32 id) {
        uint256 value = _input(o).isAddressZero() ? o.amountIn : 0;
        vm.recordLogs();
        vm.prank(o.owner);
        router.swap{value: value}(o, _userData(o));
        Vm.Log[] memory logs = vm.getRecordedLogs();
        (id, o.salt) = _createdFromLogs(logs);
        lastPlaceMatches = _matchesIn(logs);
    }

    /// @dev `AsyncOrdersMatched` legs emitted by the last `_place`.
    uint256 internal lastPlaceMatches;

    function _matchesIn(Vm.Log[] memory logs) internal view returns (uint256 n) {
        for (uint256 i; i < logs.length; ++i) {
            if (logs[i].emitter == address(hook) && logs[i].topics[0] == AsyncSwap.AsyncOrdersMatched.selector) ++n;
        }
    }

    function _createdFromLogs(Vm.Log[] memory logs) internal view returns (bytes32 id, bytes32 salt) {
        for (uint256 i; i < logs.length; ++i) {
            if (logs[i].emitter == address(hook) && logs[i].topics[0] == AsyncFiller.AsyncOrderCreated.selector) {
                id = logs[i].topics[2];
                (,,, salt) = abi.decode(logs[i].data, (bool, uint256, uint256, bytes32));
                return (id, salt);
            }
        }
        revert("no AsyncOrderCreated");
    }

    /// @dev Number of `AsyncOrdersMatched` legs since the last `vm.recordLogs()` (official `matchBook` returns nothing).
    function _countMatches() internal returns (uint256) {
        return _matchesIn(vm.getRecordedLogs());
    }

    function _fill(AsyncOrder memory o, address who) internal {
        uint256 live = _livePrice(o);
        uint256 value = _output(o).isAddressZero() ? live : 0;
        vm.prank(who);
        router.fillOrder{value: value}(o, live, "");
    }

    function _livePrice(AsyncOrder memory o) internal view returns (uint256) {
        (, uint256 net) = hook.asyncOrderInfo(o.key.toId(), _id(o));
        return net + hook.calculatePoolFee(o.key.fee, net);
    }

    function _poolFee(uint256 net) internal view returns (uint256) {
        return hook.calculatePoolFee(LPFeeLibrary.DYNAMIC_FEE_FLAG, net);
    }

    function _id(AsyncOrder memory o) internal view returns (bytes32) {
        return keccak256(abi.encode(block.chainid, o.key.toId(), o.owner, o.zeroForOne, o.salt));
    }

    function _input(AsyncOrder memory o) internal pure returns (Currency) {
        return o.zeroForOne ? o.key.currency0 : o.key.currency1;
    }

    function _output(AsyncOrder memory o) internal pure returns (Currency) {
        return o.zeroForOne ? o.key.currency1 : o.key.currency0;
    }

    function _claims(Currency c, address who) internal view returns (uint256) {
        return manager.balanceOf(who, c.toId());
    }

    function _bal(Currency c, address who) internal view returns (uint256) {
        return c.balanceOf(who);
    }

    function _open(PoolKey memory k, bytes32 id) internal view returns (bool) {
        return hook.asyncOrder(k.toId(), id) != 0;
    }

    function _amountIn(PoolKey memory k, bytes32 id) internal view returns (uint256 a) {
        (a,) = hook.asyncOrderInfo(k.toId(), id);
    }

    function _amountOutMin(PoolKey memory k, bytes32 id) internal view returns (uint256 m) {
        (, m) = hook.asyncOrderInfo(k.toId(), id);
    }

    function _priceKeyOf(PoolKey memory k, bytes32 id) internal view returns (uint128 p) {
        (,,, p,,,) = hook.orderBookOrder(k.toId(), id);
    }

    function _isBuyOf(PoolKey memory k, bytes32 id) internal view returns (bool b) {
        (,,,, b,,) = hook.orderBookOrder(k.toId(), id);
    }

    function _best(PoolKey memory k, bool isBuy) internal view returns (bytes32 id, uint128 priceKey) {
        (, priceKey, id,) = hook.bestOrder(k.toId(), isBuy);
    }

    /// @dev Official v2 exposes no open-order counter; it is the sum of the level counts of both sides'
    ///      distinct price levels among `ids`.
    function _openCount(PoolKey memory k, bytes32[] memory ids) internal view returns (uint256 n) {
        uint128[] memory seenKeys = new uint128[](ids.length);
        bool[] memory seenSide = new bool[](ids.length);
        uint256 m;
        for (uint256 i; i < ids.length; ++i) {
            if (!_open(k, ids[i])) continue;
            uint128 p = _priceKeyOf(k, ids[i]);
            bool b = _isBuyOf(k, ids[i]);
            bool seen;
            for (uint256 j; j < m; ++j) {
                if (seenKeys[j] == p && seenSide[j] == b) seen = true;
            }
            if (seen) continue;
            seenKeys[m] = p;
            seenSide[m] = b;
            ++m;
            (,, uint32 count) = hook.orderBookLevel(k.toId(), b, p);
            n += count;
        }
    }

    /// @dev The spec's price key (`_priceKey`), recomputed independently.
    function _specPriceKey(bool isBuy, uint256 amountIn, uint256 amountOut) internal pure returns (uint128) {
        uint256 price = isBuy ? Math.mulDiv(amountIn, 1e18, amountOut) : Math.mulDiv(amountOut, 1e18, amountIn);
        if (price == 0) return 1;
        if (price > type(uint128).max) return type(uint128).max;
        return uint128(price);
    }

    /* ─────────────────────────────────── signatures ─────────────────────────────────── */

    function _sign(uint256 pk, bytes32 digest) internal pure returns (bytes memory) {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(pk, digest);
        return abi.encodePacked(r, s, v);
    }

    function _hookDigest(bytes32 structHash) internal view returns (bytes32) {
        return keccak256(abi.encodePacked("\x19\x01", hook.DOMAIN_SEPARATOR(), structHash));
    }

    function _routerDigest(bytes32 structHash) internal view returns (bytes32) {
        return keccak256(abi.encodePacked("\x19\x01", router.DOMAIN_SEPARATOR(), structHash));
    }

    /// Permit2's `hashWithWitness` for `PermitWitnessTransferFrom` with the Router as spender.
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
        bytes32 tokenPermissions =
            keccak256(abi.encode(TOKEN_PERMISSIONS_TYPEHASH, Currency.unwrap(_input(o)), o.amountIn));
        bytes32 structHash = keccak256(
            abi.encode(typeHash, tokenPermissions, address(router), nonce, deadline, OrderSignatures.hashOrder(o))
        );
        bytes32 digest =
            keccak256(abi.encodePacked("\x19\x01", IPermit2Domain(Permit2Bytecode.PERMIT2).DOMAIN_SEPARATOR(), structHash));
        return _sign(pk, digest);
    }

    receive() external payable {}
}
