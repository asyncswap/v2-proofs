# AsyncSwap — Lean 4 specification and proofs

Machine-checked model of the value-carrying logic of the Async Swap v2 hook
(`../src`), written in Lean 4 against Mathlib. Every theorem is proved; there are no
`sorry`s and no axioms beyond Lean's standard ones.

```sh
# one-time: elan (Lean toolchain manager) from https://elan.lean-lang.org
lake exe cache get   # download the Mathlib build cache (~10 min first time)
lake build           # checks every proof; exit code 0 means all theorems hold
```

## What is modelled

| Lean module | Solidity | Properties proved |
| --- | --- | --- |
| `Fee.lean` | `AsyncSwap.calculatePoolFee` | The split formula equals `net·3/997`; it is exactly 30 bps of **gross**, rounded down (`fee = ⌊3·gross/1000⌋`); fee ≤ net; monotone; zero below 333 units. |
| `Arith.lean` | OpenZeppelin `Math.mulDiv` (floor / ceil) | Rounding bounds used by every other proof: ceil never under-delivers and over-delivers by < 1 denominator unit; floor never exceeds the input when `b ≤ c`. |
| `Order.lean` | `AsyncFiller.OrderInfo`, `_priceKey` | Order record, open-order well-formedness, escrow accounting per currency; `_priceKey` is always in `[1, 2^128)`. |
| `Match.lean` | `AsyncMatching._matchAmounts` | **A non-zero match never executes either side below its limit price and never overspends either escrow** (`matchAmounts_sound`). Consequently the limit prices cross (`matchAmounts_cross`), so the radix-tree price check is a filter, not the safety mechanism. Rounding favours the resting side by at most one unit (`*_tight`). |
| `Reduce.lean` | `_reduceAfterMatch`, `_settleMatchedPriorityFee` | Input accounting (`used + remaining = original`); the outstanding minimum only shrinks by what was received; **a maker closed out by any sequence of admissible matches receives at least their original `amountOutMin`** (`maker_limit_honored`), plus a refund of unused input; priority bid donated + remaining = original and the remainder fits `uint64`. |
| `Book.lean` | `AsyncSwap` / `AsyncFiller` / `AsyncMatching` state transitions | The escrow invariant from `test/MatchingInvariant.t.sol` (`invariant_escrowEqualsOutstandingObligations`) stated as `PoolState.Inv` and proved preserved by `create`, `recordPriorityFee`, `fill`, `cancel`, `updatePrice`, `fillFromPoolLiquidity` and `_matchPair`. Authorisation facts: fill needs an authorised executor, cancel needs owner-or-executor, reprice needs the owner; fill pays maker exactly `amountOutMin`, filler exactly `amountIn`, vault exactly 30 bps of gross; cancel refunds exactly the remaining escrow; filled/cancelled orders cannot be touched again; repricing moves no claims. |
| `RadixTree.lean` | `RadixPriceTree` (`insert`, `remove`, `best`, `_mostSignificantBit`) | Functional Patricia-trie model following the Solidity loops. **`best` returns the exact maximum / minimum stored price** (`best_true_spec`, `best_false_spec`, `PriceIndex.best_spec` = `invariant_bestPricesAgreeWithLinearScan`); `insert` / `remove` preserve the Patricia invariant and have exact set semantics; the tree only empties when the last leaf is removed; **every traversal visits ≤ 128 branch nodes** for `uint128` prices; the branch-free `_mostSignificantBit` routine equals `⌊log₂⌋` on its whole domain. |
| `Admin.lean` | `transferOwnership`, `acceptOwnership`, `_verify`, `invalidateNonce` | `owner` changes only through `acceptOwnership` by the nominated address; nominating never transfers control; a consumed nonce is never reusable; signatures past `deadline` are rejected. |

## Modelling choices and what is *not* covered

* **Unbounded naturals.** All amounts are `ℕ`. `Math.mulDiv` computes the 512-bit product
  exactly and reverts if the result does not fit, so `ℕ` is faithful for every
  non-reverting execution; explicit `uintN` casts are covered where they matter
  (`_priceKey`, `uint64(unfilledPriorityFee)`). Overflow of plain `+`/`*` outside
  `mulDiv` is **not** modelled.
* **Single pool, numeraire = currency1.** `PoolState` is one `AsyncFiller.State` plus one
  `Book`; the hook's per-pool mapping is a product of these.
* **Claims, not balances.** The invariant tracks the hook's ERC-6909 claim balances in the
  PoolManager, exactly as the Foundry invariant does. `invariant_assetsConserved` (PoolManager
  token backing) is a property of Uniswap v4 and is out of scope.
* **Radix tree: functional model.** `RadixTree.lean` models the trie as an inductive type and
  proves the algorithm correct. The storage encoding (`nodes` mapping with `uint32` ids,
  `parent` pointers, the `leaves` map, `_newNode` id allocation) is the remaining refinement
  gap: the proofs show the *shape* the Solidity loops build is right, not that the pointer
  updates in `insert` / `remove` realise that shape. `_matchPair` is still specified for an
  arbitrary (sell, buy) pair; per-price FIFO / priority-bid queues are not modelled.
* **Atomic transitions.** `_matchPair` burns claims in `_settleTransfers` before
  `_reduceMatchedOrders`; the model folds both into `reduceAfterMatch` per side, since the
  invariant is only required between transactions.
* **Signatures / EIP-712 / Permit2, native-ETH transient ledger, MatchingEngine harness,
  FeeVault.collect** are not modelled.

## Layout

```
lean/
├─ lakefile.toml          # Lake project, depends on Mathlib
├─ lean-toolchain         # pinned Lean version (matches Mathlib master at setup time)
├─ AsyncSwapSpec.lean     # root import
└─ AsyncSwapSpec/
   ├─ Fee.lean  Arith.lean  Order.lean
   ├─ Match.lean  Reduce.lean
   ├─ Book.lean  Admin.lean
   └─ RadixTree.lean
```
