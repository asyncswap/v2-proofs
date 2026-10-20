---
name: lean4-cleanup
description: Clear Lean 4 / Mathlib linter warnings from a lake project without changing what is proved — unused simp arguments, no-op tactics, unused `<;>`, deprecated lemma names, unused variables. Use when asked to fix lint/warnings in Lean proofs, tidy proofs after they build, or get `lake build` warning-free.
---

# Lean 4 proof cleanup

Goal: `lake build` reports no linter warnings, while every theorem still states and proves exactly what it did before.

## Hard rules

- Change only proof bodies. Never change a theorem's or def's statement or name, or the order of its explicit arguments.
- Never add `sorry`, `admit`, or `set_option linter.* false`, and never weaken a statement to get a proof through.
- If a warning can't be fixed without one of these, leave it and report it.

## Scope

- **For a person working locally:** clean what they ask for, usually the whole build.
- **For a formalmind agent working an issue, PR or protocol reconciliation:** clean only the `.lean` files your change already touches. Don't widen the diff into files the issue doesn't name. Leave warnings in other files alone, and mention them in your PR or changelog entry if they look worth a separate issue.
- **When your allowlist permits only `lake …` commands:** no pipes, `tee`, `sed`, or `sort`. Run `lake env lean <file>` per file and read its output directly, and use the Grep tool for the `sorry` check.

## Workflow

1. **Collect warnings.** Run `lake build 2>&1 | tee <scratch>/lean-warn.txt` and group the results by file and kind:
   `grep '^warning' … | sed -E 's/^warning: ([^:]+).*/\1/' | sort | uniq -c`.
   Treat this list as a starting point only. It is incomplete, because removing one unused argument often makes another one show up.
2. **Check one file at a time** with `lake env lean <file>` (run from the project root), not `lake build`.
   - It reuses the dependencies' built `.olean` files, and that's safe because statements don't change.
   - It also lets several agents work on separate files in parallel. Never run concurrent `lake build`s; they race on `.lake`.
   - Fix files in import order.
3. **Repeat until the file prints nothing**, or only warnings you have decided to keep.
4. **Final check:**
   - Run a full `lake build`.
   - Run `grep -rn --include='*.lean' -E '\bsorry\b' <libs>`.
   - Run `git diff` and confirm no line starting with `theorem`, `lemma` or `def` changed apart from `_`-prefixed binders.

## Fixes by warning kind

| Warning | Fix |
|---|---|
| `This simp argument is unused` | Delete that argument. If the list becomes `simp []`, write `simp`. Delete arguments starting from the end of the line (right to left) so the reported columns stay valid. |
| `Unused tactic linter: <;> should be replaced…` / `Used tac1 <;> tac2 where (tac1; tac2) would suffice` | Put `tac2` on its own line after `tac1`. |
| `<;> omega` is flagged, but removing it gives "no goals" or leaves goals unsolved | The first tactic closes only some branches. Wrap the earlier part in `all_goals (…)`, then add `all_goals omega` on its own line after it. |
| `X does nothing` / `this tactic is never executed` | Delete it. If it's the last branch of a `first \| a \| b`, keep only the branch that runs. |
| `(try …)` does nothing | Delete the whole `try`. |
| Deprecated `if_pos` / `if_neg` | Use `ite_eq_left` / `ite_eq_right`. They take the same arguments, so they work inside `rw [...]` too. |
| Deprecated `if_true` / `if_false` | Use `ite_true` / `ite_false`, but first check whether the simp argument is even used. Often it's unused and can just be deleted. |
| Other deprecations | Use the replacement the warning names. Check that it takes the same arguments in the same order. |
| `Variable name h is not explicitly referenced` | Rename it to `_h`. First grep for callers that pass it by name (`(h := …)`). In a `fun` or `intro`, use `_`. |
| `imports X … designed for use with the module system` | Not a lint. Moving to the `module` system needs `public import` and `public section` everywhere, which is a separate refactor. Leave it and mention it. |

## Gotchas

- **The common unused simp arguments** are `Ne.symm h`, local hypotheses (`h2`, `hpv`), `eq_self_iff_true`, `true_and`, `false_and`, `not_false_eq_true`, `add_zero`, and frame lemmas (`foo_setX`) that some other simp set already covers.
- **`simp_all [..]` vs `simp only [..]`:** `simp_all` already uses every hypothesis in context, so hypotheses passed to it explicitly are nearly always unused.
- **Unused `have`s:** removing arguments can leave a `have` that nothing uses. Lean doesn't always warn about it. Delete it if it's clearly dead, and say so in your report.
- **Speed:** a long proof can make `lake env lean` slow. Batch all the fixes for a file before re-checking rather than checking after each argument.
- **Style:** match the file's existing indentation and line layout. Don't reformat lines you aren't fixing.

## Report

For each file, list what was removed or replaced, any structural change (such as the `all_goals` split), and any warnings deliberately left with the reason. End with the final `lake build` result.
