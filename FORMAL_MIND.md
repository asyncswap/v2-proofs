# formal-mind changelog

Every run of the formal-mind bot appends one entry here, newest first. An entry records which
protocol commit was reconciled, what changed in the spec, which theorems were added, changed or
could not be proved, and what the build said. Humans may add entries too; keep the shape.

<!-- formal-mind: insert new entries directly below this line -->

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
