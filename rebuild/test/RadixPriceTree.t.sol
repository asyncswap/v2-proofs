// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Test} from "forge-std/Test.sol";
import {RadixPriceTree} from "../src/libraries/RadixPriceTree.sol";

contract RadixHarness {
    using RadixPriceTree for RadixPriceTree.Tree;

    RadixPriceTree.Tree internal tree;

    function insert(uint128 price) external returns (bool) {
        return tree.insert(price);
    }

    function remove(uint128 price) external {
        tree.remove(price);
    }

    function best(bool highest) external view returns (bool, uint128) {
        return tree.best(highest);
    }

    function contains(uint128 price) external view returns (bool) {
        return tree.contains(price);
    }

    function root() external view returns (uint32) {
        return tree.root;
    }

    function nextNodeId() external view returns (uint32) {
        return tree.nextNodeId;
    }

    function freeCount() external view returns (uint256) {
        return tree.freeIds.length;
    }

    function node(uint32 id) external view returns (RadixPriceTree.Node memory) {
        return tree.nodes[id];
    }

    function msb(uint128 v) external pure returns (uint8) {
        return RadixPriceTree._mostSignificantBit(v);
    }

    /// @dev Walks every root-to-leaf path and checks the Patricia invariant (`Trie.Wf`): at a branch with
    ///      bit `b`, every leaf on the left has bit `b` clear and every leaf on the right has it set, and all
    ///      leaves below agree with the branch's prefix above `b`. Also checks parent pointers (`Reads`).
    function checkWellFormed() external view returns (uint256 leaves) {
        uint32 r = tree.root;
        if (r == 0) return 0;
        require(tree.nodes[r].parent == 0, "root parent");
        return _check(r, 0, 0, 128);
    }

    function _check(uint32 id, uint128 prefix, uint128 mask, uint8 depth) private view returns (uint256 leaves) {
        require(depth != 0, "too deep");
        RadixPriceTree.Node storage n = tree.nodes[id];
        if (n.leaf) {
            require(n.price & mask == prefix, "prefix");
            require(tree.leaves[n.price] == id, "leaves map");
            return 1;
        }
        require(n.left != 0 && n.right != 0, "branch children");
        require(tree.nodes[n.left].parent == id && tree.nodes[n.right].parent == id, "parent ptr");
        uint128 bitMask = uint128(1) << n.bit;
        require(mask & bitMask == 0, "bit already fixed");
        uint128 childMask = mask | bitMask;
        leaves = _check(n.left, prefix, childMask, depth - 1) + _check(n.right, prefix | bitMask, childMask, depth - 1);
    }
}

/// @dev Spec: `AsyncSwapSpec/RadixTree.lean`, `RadixStorage.lean`, `Bounds.lean` (`IdAlloc`).
contract RadixPriceTreeTest is Test {
    RadixHarness h;

    function setUp() public {
        h = new RadixHarness();
    }

    function test_emptyTree() public view {
        (bool found, uint128 p) = h.best(true);
        assertFalse(found);
        assertEq(p, 0);
        assertEq(h.checkWellFormed(), 0);
    }

    function test_insertRemoveSingle() public {
        assertTrue(h.insert(5));
        assertFalse(h.insert(5)); // `created = (price ∉ keys)`
        (bool found, uint128 p) = h.best(true);
        assertTrue(found);
        assertEq(p, 5);
        assertEq(h.root(), 1);
        h.remove(5);
        assertEq(h.root(), 0); // the tree only empties when the last leaf is removed
        assertEq(h.freeCount(), 1);
        assertFalse(h.contains(5));
    }

    function test_removeAbsentReverts() public {
        h.insert(7);
        vm.expectRevert(abi.encodeWithSelector(RadixPriceTree.PriceLevelMissing.selector, uint128(8)));
        h.remove(8);
    }

    function test_bestIsExtremum() public {
        uint128[7] memory ps = [uint128(100), 3, 250, 17, 1, type(uint128).max, 64];
        for (uint256 i = 0; i < ps.length; i++) {
            h.insert(ps[i]);
        }
        (, uint128 hi) = h.best(true);
        (, uint128 lo) = h.best(false);
        assertEq(hi, type(uint128).max);
        assertEq(lo, 1);
        assertEq(h.checkWellFormed(), 7);
        h.remove(type(uint128).max);
        h.remove(1);
        (, hi) = h.best(true);
        (, lo) = h.best(false);
        assertEq(hi, 250);
        assertEq(lo, 3);
        assertEq(h.checkWellFormed(), 5);
    }

    /// @dev `IdAlloc`: ids are recycled, so the counter tracks the peak number of live keys, not the history.
    function test_idRecycling() public {
        for (uint128 i = 1; i <= 10; i++) {
            h.insert(i * 1000);
        }
        uint32 peak = h.nextNodeId();
        assertEq(peak, 19); // 2·levels − 1
        for (uint128 i = 1; i <= 10; i++) {
            h.remove(i * 1000);
        }
        assertEq(h.freeCount(), 19);
        assertEq(h.root(), 0);
        for (uint256 round = 0; round < 5; round++) {
            for (uint128 i = 1; i <= 10; i++) {
                h.insert(i * 777 + uint128(round));
            }
            assertEq(h.nextNodeId(), peak);
            assertEq(h.checkWellFormed(), 10);
            for (uint128 i = 1; i <= 10; i++) {
                h.remove(i * 777 + uint128(round));
            }
        }
        assertEq(h.nextNodeId(), peak);
    }

    /// @dev `solMsb_eq_log2`: the branch-free routine is `⌊log₂⌋` on every non-zero `uint128`.
    function testFuzz_msbIsLog2(uint128 v) public view {
        vm.assume(v != 0);
        uint8 expected;
        uint256 x = v;
        while (x > 1) {
            x >>= 1;
            expected++;
        }
        assertEq(h.msb(v), expected);
    }

    /// @dev `best_true_spec` / `best_false_spec` against a linear scan, `mem_keys_insert` / `mem_remove` set
    ///      semantics, `insert_wf` / `remove_wf`, through a random insert / remove history.
    function testFuzz_bestAgreesWithLinearScan(uint128[] memory prices, uint256 removeMask) public {
        vm.assume(prices.length > 0 && prices.length <= 24);
        uint128[] memory live = new uint128[](prices.length);
        uint256 n;
        for (uint256 i = 0; i < prices.length; i++) {
            bool created = h.insert(prices[i]);
            bool present;
            for (uint256 j = 0; j < n; j++) {
                if (live[j] == prices[i]) present = true;
            }
            assertEq(created, !present);
            if (!present) live[n++] = prices[i];
            _assertExtrema(live, n);
        }
        for (uint256 i = 0; i < prices.length; i++) {
            if ((removeMask >> i) & 1 == 0) continue;
            uint256 idx = type(uint256).max;
            for (uint256 j = 0; j < n; j++) {
                if (live[j] == prices[i]) idx = j;
            }
            if (idx == type(uint256).max) {
                vm.expectRevert(abi.encodeWithSelector(RadixPriceTree.PriceLevelMissing.selector, prices[i]));
                h.remove(prices[i]);
                continue;
            }
            h.remove(prices[i]);
            live[idx] = live[n - 1];
            n--;
            _assertExtrema(live, n);
        }
    }

    function _assertExtrema(uint128[] memory live, uint256 n) private view {
        (bool found, uint128 hi) = h.best(true);
        (, uint128 lo) = h.best(false);
        assertEq(found, n != 0);
        assertEq(h.checkWellFormed(), n);
        if (n == 0) return;
        uint128 max;
        uint128 min = type(uint128).max;
        for (uint256 j = 0; j < n; j++) {
            if (live[j] > max) max = live[j];
            if (live[j] < min) min = live[j];
            assertTrue(h.contains(live[j]));
        }
        assertEq(hi, max);
        assertEq(lo, min);
    }
}
