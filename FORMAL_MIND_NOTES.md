# formal-mind notes

## asyncswap/v2 @ 66c2e20ec644871482232f785cb01a4ea6d37cbc

**Change:** `src/libraries/RadixPriceTree.sol` recycles node ids. `remove` now calls
`_freeNode` (delete + push onto `freeIds`) for the removed leaf and, unless it was the root,
its parent branch; `_newNode` pops from `freeIds` before incrementing `nextNodeId`.

**Spec impact:**

- `AsyncSwapSpec/RadixTree.lean` abstracts node ids away (inductive `Trie`), so `insert`,
  `remove` and `best` and every theorem about them are unchanged. Reusing an id cannot alias
  a live node because `remove` rewires the parent, sibling and `leaves` entries before
  freeing it. This matches the contract comment, and the functional trie has no ids to
  alias.
- `AsyncSwapSpec/Bounds.lean` already modelled this allocator (`IdAlloc`, roadmap item 7).
  I checked it against the Solidity. `insert` takes `min need free` ids from the free list
  and grows `next` by the rest, where `need` is 1 for an empty tree and 2 otherwise.
  `remove` releases 1 id for the root leaf and 2 otherwise. No definition changes were
  needed.
- **New:** `IdAlloc.Bounded`, `bounded_empty`, `bounded_insert`, `bounded_remove`, `run`,
  `run_bounded`, `run_next_le_peak`. These prove the `hfree` hypothesis of
  `IdAlloc.next_le_peak` and `IdAlloc.insert_no_overflow` from the empty tree for every
  insert/remove history. So `nextNodeId ≤ liveIds peak` is now a theorem about reachable
  states, not an assumption.

No theorem statements changed. There are no unproven gaps, no `sorry` and no new axioms.
