// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Test} from "forge-std/Test.sol";
import {ProtocolFee} from "../src/libraries/ProtocolFee.sol";

/// @dev Spec: `AsyncSwapSpec/Fee.lean`.
contract ProtocolFeeTest is Test {
    /// `poolFee_eq`: the split form equals `net * 3 / 997`.
    function testFuzz_splitFormEqualsStraightforward(uint256 net) public pure {
        net = bound(net, 0, type(uint256).max / 3);
        assertEq(ProtocolFee.poolFee(net), net * 3 / 997);
    }

    /// `poolFee_eq_30bps_of_gross`: exactly 30 bps of gross, rounded down.
    function testFuzz_thirtyBpsOfGross(uint256 net) public pure {
        net = bound(net, 0, type(uint256).max / 4);
        uint256 fee = ProtocolFee.poolFee(net);
        assertEq(fee, 3 * (net + fee) / 1000);
    }

    /// `poolFee_le_net`, `poolFee_mono`, `poolFee_eq_zero_iff`.
    function testFuzz_boundsAndMonotone(uint256 a, uint256 b) public pure {
        a = bound(a, 0, type(uint256).max / 4);
        b = bound(b, 0, type(uint256).max / 4);
        assertLe(ProtocolFee.poolFee(a), a);
        if (a <= b) assertLe(ProtocolFee.poolFee(a), ProtocolFee.poolFee(b));
        assertEq(ProtocolFee.poolFee(a) == 0, a < 333);
    }

    /// `poolFee_lt_two_pow_256`: no overflow on the whole `uint256` range.
    function test_noOverflowAtMax() public pure {
        uint256 fee = ProtocolFee.poolFee(type(uint256).max);
        assertLe(fee, type(uint256).max);
        assertEq(fee, (type(uint256).max / 997) * 3 + ((type(uint256).max % 997) * 3) / 997);
    }
}
