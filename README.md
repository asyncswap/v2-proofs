# asyncswap/v2-proofs

Lean 4 + Mathlib specification and machine-checked proofs for the Async Swap protocol.

| Library | Scope | Reference source |
| --- | --- | --- |
| `AsyncSwapSpec` | v2 hook: protocol fee, order matching, partial fills, escrow invariant, admin, `RadixPriceTree` | `asyncswap/v2` `src/` |
| `AsyncSwapProtocol` | Call-sequence state machine from the README sequence diagram: Router → PoolManager → hook → FeeVault, token ledgers, claims, deltas. `AsyncSwapProtocol/V2/` extends it to v2 (priority bids, matching, liquidity fills, NativeClaims) with lifecycle, settlement, delta neutrality, backing, escrow and conservation theorems | v1: `AsyncSwap Production/packages/protocol/src` @ `fcf75d4`; v2: `asyncswap/v2` `src/` |

`lake build` checks every theorem. No `sorry`, no extra axioms. See [README.spec.md](README.spec.md)
for the theorem-by-theorem map of `AsyncSwapSpec`, and the module docstrings in
`AsyncSwapProtocol/` for the protocol model.

```sh
lake exe cache get   # Mathlib build cache
lake build
```

CI runs `lake build` only on pushes to `main` (`.github/workflows/lean.yml`); pull requests are reviewed, not built.
Pushes to the protocol repositories trigger the formal-mind bot (`.github/workflows/formal-mind.yml`),
which updates the spec for the new commit and opens a pull request here.

## Decisions and assumptions

These were put to the maintainer on 2026-10-15 and answered as recorded. Every theorem in
this repository should be read against them; change them here first if the protocol changes.

### Decisions (questionnaire and answers)

| # | Question | Answer | Consequence for the spec |
| --- | --- | --- | --- |
| 1 | Same-price priority in v2 matching: what rule should the spec prove? | **Bid first, then FIFO.** In `PriorityFee` mode a higher USDC bid matches first and equal bids fall back to sequence order; in `FIFO` mode sequence order only. A reprice re-enters at the back of its level. | Price-time-priority theorems target exactly the code's `_priorityKey = (fee << 64) \| (maxUint64 − sequence)` ordering and `updatePrice`'s `sequence = ++nextSequence`. |
| 2 | Arithmetic model | **Unbounded ℕ/ℤ plus explicit bounds.** Amounts stay unbounded; per-entry-point theorems state the input bounds under which no intermediate exceeds `2^256` (and `uint128` / `uint64` for price keys and bids). | No wraparound semantics anywhere. A theorem about overflow is always of the form "under these input bounds, this intermediate is < 2^N". |
| 3 | Target contracts for the call-sequence state machine (`AsyncSwapProtocol`) | **Extend to v2.** One model should cover the active codebase: priority-bid escrow in the create unlock, `matchNewOrder`, `matchBook`, `fillFromPoolLiquidity`, `NativeClaims`. | `AsyncSwapProtocol` currently mirrors the production repo at `fcf75d4`; the v2 extension is the next milestone (see roadmap). |
| 5 | Fix for radix node-id exhaustion (2026-10-16) | **Recycle freed ids**, keep `uint32`. Rejected: widen to `uint64` (two-slot `Node`), accept-and-document. | `remove` releases ids to a free list; the spec's exhaustion assumption becomes a theorem about the peak number of live levels. |
| 4 | Periphery in verified scope | **All of:** radix-tree storage refinement; native-ETH transient ledger (incl. v2 `NativeClaims`); EIP-712 / Permit2 struct hashing and witness binding; `FeeVault.collect` and `sweep`. | Signature validity moves from an abstract oracle to a hashing model; the pointer-level `RadixPriceTree` gets a refinement proof against `AsyncSwapSpec/RadixTree.lean`. |

### Standing modelling assumptions

- **keccak256 is injective** on the tuples the contracts hash: order ids are modelled as the
  preimage `(owner, zeroForOne, salt)`; the hook's salt collision walk is modelled as "the
  chosen slot is free".
- **Uniswap v4 PoolManager** is modelled by its accounting contract: per-locker currency
  deltas that must net to zero at the end of `unlock`, ERC-6909 claims, `settle` / `take` /
  `mint` / `burn`, and the `BeforeSwapDelta` accounting for a hook that consumes the whole
  exact input. Pool math (`_swap`, liquidity, LP fees) is out of scope except where
  `fillFromPoolLiquidity`'s result is taken as an input satisfying its own checks.
- **One pool per model**, currency0 / currency1, with the numeraire (USDC) as currency1 and
  only currency0 possibly native. Multi-pool state is a product of these.
- **Ledgers are signed integers** so conservation is unconditional; non-negativity is a
  proved invariant, not a modelling assumption.
- **Signatures** (`SignatureChecker`, ERC-1271, Permit2) are an oracle over the exact fields
  each struct hash commits to, until decision 4's hashing model lands.
- **Events, gas and reverts' reasons** are not modelled; a transaction is `Option World`.
- **Fewer than `2^31` price levels are stored at once** per radix tree. With id recycling
  (roadmap item 7, decision: recycle) this is the only way `insert` can revert on ids
  (`Bounds.lean` `IdAlloc.insert_no_overflow`); it would require `2^31` live storage slots.
- **The reference commits** are `asyncswap/v2` (working tree as of 2026-10-15) for
  `AsyncSwapSpec` and `AsyncSwap Production/packages/protocol` @ `fcf75d4` for
  `AsyncSwapProtocol`. The formal-mind bot re-pins on every protocol push.

## Findings worth a contract-side look

- **Radix node ids were never reused** (found 2026-10-15, fixed 2026-10-16 by recycling):
  each new distinct price level cost two fresh `uint32` ids and `remove` freed none, so after
  `2^31 − 1` distinct levels a tree's `insert` would revert with `NodeIdOverflow` forever.
  `RadixPriceTree.remove` now releases ids to a free list that `_newNode` reuses;
  `Bounds.lean` (`IdAlloc.insert_no_overflow`) proves the counter tracks the *peak* number
  of simultaneously stored prices, so overflow needs `2^31` prices stored at once.
- **`_priceKey` can revert for huge inputs** (`priceKey_mulDiv_lt`): `mulDiv(amount, 1e18,
  other)` overflows `uint256` once `amount ≥ 2^256 / 1e18 ≈ 1.16e58`, which would make
  `addOrder` revert for such an order. Harmless for real tokens; stated as the input bound.

## Roadmap

1. ~~**v2 state machine**~~ — done (`AsyncSwapProtocol/V2/Model.lean`, `Spec.lean`,
   `Settlement.lean`).
2. ~~**Global invariants**~~ — done: `Backing` (PoolManager balance = claim supply + pool
   reserves), `Escrow` (hook claims = open input + escrowed bids), `step_conservation`
   (per-currency totals over all ledgers). Non-negativity of balances remains open.
3. ~~**Price-time priority**~~ — done (`AsyncSwapSpec/Priority.lean`): bid first, then FIFO;
   reprice re-enters last; the matched level is the best price.
4. ~~**Bounds**~~ — done (`AsyncSwapSpec/Bounds.lean`): per-site overflow bounds, `uint64`
   sequence and `uint32` radix node-id longevity bounds.
5. **Radix tree refinement** (decision 4): pointer-level `RadixPriceTree` ≈ functional trie.
6. **Hashing model** (decision 4): EIP-712 / Permit2 struct hashes and witness binding.
7. ~~**Node-id exhaustion fix**~~ — decision: **recycle freed ids** (keeps the one-slot
   `Node`). Implemented in `asyncswap/v2` `RadixPriceTree.sol` (free list popped by
   `_newNode`), with the allocator proved in `Bounds.lean`.
