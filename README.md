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

`FORMAL_MIND.md` is the changelog of every bot run (and of human changes that touch theorems).
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
| 6 | How to model `keccak256` for EIP-712 / Permit2 (2026-10-16) | **Symbolic preimages + collision-freedom.** `keccak256` is an arbitrary injective function on the preimages the contracts build (type strings, `abi.encode` word tuples, the EIP-712 envelope). Rejected: concrete Keccak (no proof leverage), identity "hash" (unfaithful). | Binding theorems are exact: a signature commits to precisely the listed fields, and `sqrtPrice` / `salt` are provably *not* covered by the Permit2 witness (by design: v4 never reads the limit, the hook assigns the salt). |
| 4 | Periphery in verified scope | **All of:** radix-tree storage refinement; native-ETH transient ledger (incl. v2 `NativeClaims`); EIP-712 / Permit2 struct hashing and witness binding; `FeeVault.collect` and `sweep`. | Signature validity moves from an abstract oracle to a hashing model; the pointer-level `RadixPriceTree` gets a refinement proof against `AsyncSwapSpec/RadixTree.lean`. |
| 7 | Partially filled orders whose price changes (2026-10-17, cycle 1) | **Follow v2:** a partial fill that changes an order's price key gives it a new sequence, so it goes to the back of its new level, like a reprice. | The rebuild re-sequences on partial fills; the priority theorems should cover the reduced order too. |
| 8 | Compatibility with deployed v2 (2026-10-17, cycle 1) | **Stay compatible with v2:** EIP-712 domains `"AsyncSwap","1"` and `"AsyncSwap Router","1"`, the `HookSwap` event, and v2's external interface, so v2's own test suite runs against the rebuild. | The official rebuild keeps v2's ABI; its internals may stay simpler. |
| 9 | Improvements found by the rebuild (2026-10-17, cycle 1) | **Accept all:** the priority bid is escrowed in the same unlock that creates the order (no separate `recordPriorityFee` step or escrowed flag); the maker chooses the salt (the id is known before sending; the hook walks `salt = keccak256(salt)` past a used id and reports the final salt); every test is named after the theorem it checks. | Carried into the official rebuild, and candidates to carry back into v2. |
| 10 | Gaps found by the rebuild (2026-10-17, cycle 1) | **Follow v2:** USDC on either side of a pool, pools must hold USDC and use a dynamic fee, pool fills charge a fixed 0.30% LP fee, and a new order falls back to pool liquidity after matching. | Findings for the spec: the model fixes the numeraire to `currency1` and does not model the fallback or the fee override. |

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
- **Signatures** (`SignatureChecker`, ERC-1271, Permit2) are an oracle over the digest the
  maker signed; `Hashing.lean` says which fields that digest commits to (decision 6). The
  only property of `keccak256` used is collision-freedom on the symbolic preimages the
  contracts hash (type strings, `abi.encode` tuples, the `\x19\x01` envelope).
- **A pool's two currencies differ** (`currency0 < currency1`, enforced by Uniswap v4); only
  under this does the Permit2 witness pin the order's direction (`tokens_inj`).
- **Events, gas and reverts' reasons** are not modelled; a transaction is `Option World`.
- **Fewer than `2^31` price levels are stored at once** per radix tree. With id recycling
  (roadmap item 7, decision: recycle) this is the only way `insert` can revert on ids
  (`Bounds.lean` `IdAlloc.insert_no_overflow`); it would require `2^31` live storage slots.
- **The reference commits** are `asyncswap/v2` @ `66c2e20` for
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
5. ~~**Radix tree refinement**~~ (decision 4) — done (`AsyncSwapSpec/RadixStorage.lean`,
   `RadixRemove.lean`, `RadixInsert.lean`): the storage model (`nodes` mapping, `parent`
   pointers, `leaves` map, `_newNode` free list) with `insert`, `remove` and `best` written as
   `RadixPriceTree.sol` writes them; `Repr` relates storage to the functional trie, and
   `PriceIndex.best_refines`, `PriceIndex.insert_refines`, `PriceIndex.remove_refines` show
   each operation stores exactly the verified `PriceIndex` operation (`remove` of an absent
   price is the `PriceLevelMissing` revert, `insert` reports `created` iff the price was new).
6. ~~**Hashing model**~~ (decisions 4, 6) — done (`AsyncSwapSpec/Hashing.lean`): symbolic
   `keccak256` assumed collision-free; `OrderSignatures.sol` struct hashes, OpenZeppelin
   domain separator / digest, Permit2 witness struct hash and `orderId` transcribed; witness
   binding for `swapWithSig`, `setExecutorWithSig`, `updatePriceWithSig`, `cancelWithSig`;
   type separation between every struct type; domain separation across contracts and chains.
7. ~~**Node-id exhaustion fix**~~ — decision: **recycle freed ids** (keeps the one-slot
   `Node`). Implemented in `asyncswap/v2` `RadixPriceTree.sol` (free list popped by
   `_newNode`), with the allocator proved in `Bounds.lean`.
