# The rebuild cycle

This is the algorithm the swarm runs, end to end. Every role reads it to know where it is.

## Inputs

- **The draft.** The maintainer's own protocol, `asyncswap/v2` (checked out read-only under
  `protocol/`). The maintainer keeps building it however they like.
- **Intent.** New behaviour the maintainer describes in words (on the Assistant notebook, #69)
  that is not in the code yet. The assistant files it as an issue labelled `fm:intent`, and it
  counts as a protocol change just like a commit.

## What we produce

Two Solidity projects and two proof systems, kept in step:

| | Solidity | Lean |
| --- | --- | --- |
| draft | `protocol/` (the maintainer's v2) | `AsyncSwapSpec/`, `AsyncSwapProtocol/` (spec **S**) |
| rebuild | `rebuild/` (built from the proofs only) | `RebuildSpec/` (spec **S′**, proved from the rebuild) |

## One cycle

Cycle `k` runs these phases in order. The editor decides when a phase is finished and records
it on the ledger as `<!-- fm-cycle n=<k> phase=<phase> -->`.

1. **spec.** The provers formalize the draft and every open `fm:intent` until **S** is near
   complete: the planner has nothing left that models the draft, and no `fm:finding` is open.
   This is what the swarm has been doing from the start.
2. **rebuild.** The rebuilder builds `rebuild/` from **S** alone. It never reads the draft.
   Whatever it cannot decide from the proofs, it decides simply and writes down in
   `rebuild/README.md` ("What the proofs did not determine"). That list is the first
   measure of how complete **S** is.
3. **compare.** The editor reads the draft and the rebuild side by side and classifies every
   difference:
   - **gap**: the draft does something the rebuild does not, because **S** does not say it.
     That is a spec gap (`fm:finding` for the planner) and a rebuild fix (`fm:rebuild`).
   - **improvement**: the rebuild is simpler or safer and still satisfies **S**. The
     maintainer decides whether the draft should take it (via the assistant).
   - **divergence**: they differ and neither is clearly right. The maintainer decides.
   - **bug**: the rebuild or the draft breaks a theorem or an invariant. Reported at once.
   Each decision goes to the maintainer as one question through `/ask assistant`, with the
   editor's recommendation. Nothing is changed on a guess.
4. **polish.** The rebuilder applies the decided fixes, the provers prove the new findings
   into **S**, and the editor re-compares until every difference is closed or recorded as a
   decision in `README.md`. This is the editor's cycle: tighten, simplify, re-check.
5. **reprove.** The provers write **S′** from the rebuild (`RebuildSpec/`), the same way **S**
   was written from the draft, without copying **S**. Then the editor compares **S** with **S′**:
   a theorem in one and not the other is either a missing proof (queue it), an over-strong
   assumption (a finding), or a real behavioural difference (back to compare).
6. **close.** The editor writes the cycle's summary on the ledger: differences found, how
   each was resolved, theorems added to **S** and **S′**, invariants added to the rebuild, and
   the confidence (below). Then the next cycle starts at **spec**, or the swarm rests.

## When to start a new cycle

A cycle is triggered by change, not by the clock:

- a draft commit that the bot's reconcile entry in `FORMAL_MIND.md` says changes behaviour
  (spec impact other than "None"), or
- a new `fm:intent`, or
- a finding from the previous cycle that changed **S**.

Changes that do not affect behaviour (comments, tests, gas only) are noted and do not restart
anything. Intent goes through the cycle like code: it is specified in **S** first, the
rebuild implements it from **S**, and the comparison then shows whether the draft does it yet.
When it does not, the assistant tells the maintainer what to build.

## The end state

The cycles stop when all of these hold, and the editor says so in its close summary:

- **agreement**: every difference between the draft and the rebuild is closed or a recorded
  decision;
- **two specs agree**: every theorem in **S** has a counterpart in **S′** and the other way round,
  or the difference is recorded;
- **a fixed point**: the last cycle found no new gap, divergence or bug;
- **no open questions**: nothing is waiting on the maintainer.

Plan for two to five cycles: two when the draft is stable and the first comparison is clean,
up to five when each cycle keeps finding behaviour. After five, the editor stops and asks the
maintainer whether the design itself is still moving.

**Confidence** in the close summary is one of: **low** (open gaps or bugs), **medium**
(agreement, but **S′** is incomplete), **high** (the end state holds), with the reason.

## Asking the right questions

The point of every phase is to surface what the maintainer has not said. When a role has to
choose behaviour that neither the proofs nor a recorded decision fixes, it does not guess
silently: the rebuilder writes the choice down, and the editor turns every such choice into a
question for the maintainer through the assistant. One question per decision, phrased so it can
be answered in a line, recommendation first.
