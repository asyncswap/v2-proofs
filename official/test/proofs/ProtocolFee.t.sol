// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {ProofBase} from "./ProofBase.sol";
import {LPFeeLibrary} from "v4-core/libraries/LPFeeLibrary.sol";

/// @dev Spec: `AsyncSwapSpec/Fee.lean`. Official v2 has no `ProtocolFee` library; the fee is
///      `AsyncSwap.calculatePoolFee(uint24, uint256)` (the fee tier argument is ignored).
contract ProofProtocolFeeTest is ProofBase {
    function _fee(uint256 net) internal view returns (uint256) {
        return hook.calculatePoolFee(LPFeeLibrary.DYNAMIC_FEE_FLAG, net);
    }

    /// `poolFee_eq`: the split form equals `net * 3 / 997`.
    function testFuzz_splitFormEqualsStraightforward(uint256 net) public view {
        net = bound(net, 0, type(uint256).max / 3);
        assertEq(_fee(net), net * 3 / 997);
    }

    /// `poolFee_eq_30bps_of_gross`: exactly 30 bps of gross, rounded down.
    function testFuzz_thirtyBpsOfGross(uint256 net) public view {
        net = bound(net, 0, type(uint256).max / 4);
        uint256 fee = _fee(net);
        assertEq(fee, 3 * (net + fee) / 1000);
    }

    /// `poolFee_le_net`, `poolFee_mono`, `poolFee_eq_zero_iff`.
    function testFuzz_boundsAndMonotone(uint256 a, uint256 b) public view {
        a = bound(a, 0, type(uint256).max / 4);
        b = bound(b, 0, type(uint256).max / 4);
        assertLe(_fee(a), a);
        if (a <= b) assertLe(_fee(a), _fee(b));
        assertEq(_fee(a) == 0, a < 333);
    }

    /// `poolFee_lt_two_pow_256`: no overflow on the whole `uint256` range.
    function test_noOverflowAtMax() public view {
        uint256 fee = _fee(type(uint256).max);
        assertLe(fee, type(uint256).max);
        assertEq(fee, (type(uint256).max / 997) * 3 + ((type(uint256).max % 997) * 3) / 997);
    }
}
