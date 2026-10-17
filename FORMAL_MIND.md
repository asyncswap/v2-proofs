# formal-mind changelog

Every run of the formal-mind bot appends one entry here, newest first. An entry records which
protocol commit was reconciled, what changed in the spec, which theorems were added, changed or
could not be proved, and what the build said. Humans may add entries too; keep the shape.

<!-- formal-mind: insert new entries directly below this line -->

## 2026-10-17 — asyncswap/v2-proofs issue #61 — spec: pool reserves and claim supply stay non-negative across every v2 entry point

**Trigger:** swarm issue #61.

**Contract change.** None.

**Spec impact.** New `AsyncSwapProtocol/V2/SupplyNonNeg.lean`, imported from the `AsyncSwapProtocol`
root. No other module touched. The model has no `Backing` invariant, and nothing else ties
`claimsSupply` to the claim balances. So the module first proves `SupplyEq` as its own
preserved invariant: `claimsSupply c = Σ a ∈ S, claims c a` over a finite support `S`. The
support is needed because `Address = ℕ`.

**Theorems added.** `ReservesNonNeg`; `SupplyEq`; `SupplyEq.bump` (`mint`/`burn` keep it);
`claimsSupply_nonneg` (`SupplyEq` plus `ClaimsNonNeg` give `0 ≤ claimsSupply c`); the `Tracks`
relation (reserves only grow, `SupplyEq` carries over), with one lemma per ledger op and per body;
`liquidityFill_inv`; `step_supply_inv`, `step_reserves_nonneg`, `step_supplyEq` (every v2 entry
point, no hypothesis); `step_claimsSupply_nonneg` (under the hypotheses of `step_claims_nonneg`).

**Theorems changed or weakened.** None.

**Unproven gaps.** None. No hypothesis was added for reserves: `liquidityFillGuard` already
requires `amountOut ≤ reserves o.output` (`Model.lean:435`). `poolSwap` in
`fillFromPoolLiquidity` is the only reserve debit, and its input and output currencies differ.

**Build.** `lake build` clean, no `sorry`, no new axioms.

## 2026-10-17 — asyncswap/v2-proofs issue #60 — spec: wallet balances outside the PoolManager stay non-negative across every v2 entry point

**Trigger:** swarm issue #60.

**Contract change.** None.

**Spec impact.** New `AsyncSwapProtocol/V2/BalNonNeg.lean`, imported from the `AsyncSwapProtocol`
root. `Model.lean`, `Invariants.lean` and `ClaimsNonNeg.lean` untouched. The issue suggested a
`Grows`-style relation. Wallet balances can go down, though, so the module uses per-op
preservation lemmas whose debit steps take a balance hypothesis instead.

**Theorems added.** `BalNonNeg` (`∀ c a, a ≠ cfg.pm → 0 ≤ w.bal c a`); `BalNonNeg.of_bal_eq`;
one preservation lemma per ledger op (`BalNonNeg.transfer` and `BalNonNeg.settle`, which take
`n ≤ bal c payer`; `take`, `payOut`, `mint`, `burn`, `poolSwap`, `setOrder`, `deleteOrder`,
`setPendingNative`); one per hook and entry body (`payOutBody`, `settleBidBody`,
`reduceSideBody`, `matchLoop`, `createBody`, `priorityFeeBody`, `liquidityFillBody`,
`cancelBody`, `fillBody`); `bal_createBody`; `step_bal_nonneg` (every v2 entry point preserves
`BalNonNeg`, under the same environment hypotheses as `step_escrow`, except the gap below).

**Theorems changed or weakened.** None.

**Unproven gaps.** A buy-side `swap` (`o.input = numeraire`) with a non-zero `priorityFee`
debits the owner's numeraire twice, `amountIn` in `createBody` and then `priorityFee` in
`priorityFeeBody`. `swapGuard` checks each one against the starting balance on its own
(`Model.lean:341-343`) and never checks their sum, so in the model that swap can drive the owner
negative. `step_bal_nonneg` leaves out exactly that case through the hypothesis
`hgap : a = .swap s o v up ms → o.input = numeraire → o.priorityFee = 0`. It makes no assumption
about balances. Every other debit is guarded.

**Build.** `lake build` clean, no `sorry`, no new axioms.

## 2026-10-16 — asyncswap/v2-proofs issue #52 — spec: user claim balances stay non-negative across every v2 entry point

**Trigger:** swarm issue #52.

**Contract change.** None.

**Spec impact.** New `AsyncSwapProtocol/V2/ClaimsNonNeg.lean`, imported from the
`AsyncSwapProtocol` root. `Invariants.lean`, `Settlement.lean` and `NonNeg.lean` untouched; the
`Finset.sum_nonneg` fact for `owed` is re-proved locally (`owed_nonneg'`) so this module does not
depend on PR #51.

**Theorems added.** `ClaimsNonNeg` (`∀ c a, 0 ≤ w.claims c a`); `Grows` (between two points of a
transaction no claim balance off the hook went down) with `grows_refl`, `grows_trans` and one
`grows_*` lemma per ledger operation and hook body (`grows_mint`, `grows_burn_hook`,
`grows_payOutBody`, `grows_settleBidBody`, `grows_matchLoop`, `grows_fillBody`,
`grows_cancelBody`, `grows_liquidityFillBody`, …); `ClaimsNonNeg.of_grows` (off-hook balances
from `Grows`, the hook's from `Escrow` after the step); `redeemNative_claims_nonneg` (the burn is
guarded by `amount ≤ claims false sender`); `step_claims_nonneg` (every v2 entry point preserves
`ClaimsNonNeg`, under `Escrow` and the same environment assumptions as `step_escrow`).

**Theorems changed or weakened.** None.

**Unproven gaps.** No entry point debits an off-hook claim without a guard in the model: every
`burn` in a hook body burns the hook's own claim, and `redeemNative` checks the caller's balance
first. So `step_claims_nonneg` needs no extra hypothesis. Still open: non-negativity of
PoolManager-side totals (`Backing`) and of the native-ETH ledger entries.

**Build.** `lake build` clean, no `sorry`, no new axioms.

## 2026-10-16 — asyncswap/v2-proofs issue #46 — spec: hook claim balances are non-negative under Escrow

**Trigger:** swarm issue #46 (taken by the maintainer).

**Contract change.** None.

**Spec impact.** New `AsyncSwapProtocol/V2/NonNeg.lean`, imported from the `AsyncSwapProtocol`
root. `Invariants.lean` untouched.

**Theorems added.** `escrowOf_nonneg` (one open order's obligation is ≥ 0: `split_ifs <;> omega`
over the natural-number fields), `owed_nonneg` (`Finset.sum_nonneg`),
`Escrow.hook_claims_nonneg` (under `Escrow`, `0 ≤ w.claims c cfg.hook` for every currency),
`step_hook_claims_nonneg` (after any v2 entry point, via `step_escrow`, same environment
assumptions).

**Theorems changed or weakened.** None.

**Unproven gaps.** Still open: non-negativity of user (maker / filler) claim balances, of
PoolManager-side totals (`Backing`), and of the native-ETH ledger entries (signed deltas by
construction); these need per-entry-point arguments, not the escrow equation.

**Build.** `lake build` clean, no `sorry`, no new axioms.

## 2026-10-16 — asyncswap/v2 @ afd161b — (commit title not available to the bot)

**Trigger:** push to `asyncswap/v2` (`repository_dispatch`), commit
`afd161be167c925ce68ef7a75eadf85097f12fac`.

**Contract change.** `src/libraries/RadixPriceTree.sol` (+23 / −4): `Tree` gains
`uint32[] freeIds`; a new `_freeNode` deletes a node and pushes its id to `freeIds`; `remove`
calls `_freeNode` where it used to `delete` (the root leaf in the root case; the branch and
then the leaf otherwise); `_newNode` pops the last element of `freeIds` before incrementing
`nextNodeId`. The library doc comment now describes the recycling. This is the same change
recorded in the 66c2e20 entry below. The commit message could not be read from the sandbox,
so the heading leaves the title out.

**Spec impact.** None. The spec already models this change exactly, so no Lean file changed.
Checked against the Solidity at `afd161b`:
- `AsyncSwapSpec/RadixStorage.lean`: `Tree.freeIds : List ℕ` has the most recent push at the
  head. `Tree.newNode` pops the head when the list is non-empty and otherwise returns
  `nextNodeId + 1`. `Tree.freeNode` resets the node to `Node.empty` and conses the id.
  `Tree.relink` frees `branchId` and then `leafId`, so the leaf ends up on top of the stack, as
  in Solidity. In the root case `Tree.remove` frees the leaf and sets `root := 0`; the two
  writes touch different fields, so their order does not matter.
- `AsyncSwapSpec/Bounds.lean`: the `IdAlloc` counting abstraction (1 id per insert into an
  empty tree and 2 otherwise, taken from the free list first; 1 released by a root remove and 2
  otherwise) still matches.
- `AsyncSwapSpec/RadixTree.lean` (functional trie with no ids) and `AsyncSwapProtocol/*` are
  unaffected.

**Theorems added.** None. **Theorems changed or weakened.** None. `best_refines`,
`insert_refines`, `remove_refines` (whose `Repr` invariant includes `ids_fresh`, `free_fresh`
and `free_nodup`) and the `IdAlloc` bounds were rechecked by the build and still hold.
**Unproven gaps.** None. **Build.** `lake build` clean (3167 jobs; only the existing
unreachable-tactic linter warnings in `AsyncSwapProtocol/V2/Invariants.lean`), no `sorry`, no
`admit`, no new axioms.

## 2026-10-16 — asyncswap/v2 @ 6cf3ac5 — (commit title not available to the bot)

**Trigger:** push to `asyncswap/v2` (`repository_dispatch`), commit
`6cf3ac56644f6242accfa81f08f14a123e847b28`.

**Contract change.** None under `src/`. `protocol-diff.txt` is empty: `git diff --stat HEAD~1
HEAD -- src` succeeded (the workflow writes `(no parent)` if the parent is missing), so the
commit has a parent and changes no file in `src/`. The commit message could not be read from
the sandbox, so the heading leaves the title out.

**Spec impact.** None. `AsyncSwap.sol`, `AsyncFiller.sol`, `AsyncMatching.sol`,
`RadixPriceTree.sol` and the Router / PoolManager / hook sequence are unchanged, so no Lean
definition in `AsyncSwapSpec/*` or `AsyncSwapProtocol/*` changed.

**Theorems added.** None. **Theorems changed or weakened.** None. **Unproven gaps.** None.
**Build.** `lake build` clean (3165 jobs; only existing unreachable-tactic linter warnings in
`AsyncSwapProtocol/V2/Invariants.lean`), no `sorry`, no new axioms.

## 2026-10-16 — asyncswap/v2 @ 66c2e20 — fix(radix): recycle node ids released by remove

**Trigger:** push to `asyncswap/v2` (`repository_dispatch`), run
[38835686368](https://github.com/asyncswap/v2-proofs/actions/runs/38835686368), 9 turns.
**Merged as:** [#20](https://github.com/asyncswap/v2-proofs/pull/20).

**Contract change.** `RadixPriceTree.remove` now releases the removed leaf and (unless it was
the root) its parent branch to `freeIds`; `_newNode` pops from `freeIds` before incrementing
`nextNodeId`.

**Spec impact.**
- `AsyncSwapSpec/RadixTree.lean`: unchanged. The functional trie has no node ids, so `insert`,
  `remove`, `best` and their theorems are unaffected. Reusing an id cannot alias a live node
  because `remove` rewires parent, sibling and `leaves` before freeing.
- `AsyncSwapSpec/Bounds.lean`: the `IdAlloc` allocator already matched the Solidity (checked:
  `insert` takes `min need free` ids from the free list, `need` is 1 for an empty tree and 2
  otherwise; `remove` releases 1 for the root leaf and 2 otherwise). No definition changed.

**Theorems added.** `IdAlloc.Bounded`, `bounded_empty`, `bounded_insert`, `bounded_remove`,
`run`, `run_bounded`, `run_next_le_peak`: the free-list hypothesis of `next_le_peak` and
`insert_no_overflow` is now proved for every insert/remove history from an empty tree, so
`nextNodeId ≤ liveIds peak` is a theorem about reachable states, not an assumption.

**Theorems changed or weakened.** None. **Unproven gaps.** None. **Build.** `lake build`
clean, no `sorry`, no new axioms.
