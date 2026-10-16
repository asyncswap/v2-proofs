# The formalmind swarm

A small team of bots that owns the Lean specification in this repository and keeps working
on the roadmap in `README.md`, hands off, within a spend budget. All of them post as
**formalmind[bot]**; the bold word at the start of a comment says which role is talking,
and roles hand work to each other by tagging `@fm-prover`, `@fm-reviewer`, `@fm-merger` or
`@fm-planner` in their comments. Humans are tagged as `@mmsaki` when a decision is needed.
Nobody ever writes `@formalmind` (that summons the chat bot, which is a different workflow).

## Shared memory is GitHub

| Thing | Meaning |
| --- | --- |
| Issue labelled `fm:todo` | a scoped unit of work the planner wrote, queued for a prover |
| `fm:in-progress` | a prover is on it; its branch is `fm/issue-<n>` |
| `fm:blocked` | needs a human; the comment says what question is open |
| PR labelled `fm:review` | the prover is done and the reviewer should look |
| `fm:changes` | the reviewer or merger bounced it back to the prover |
| `fm:needs-rebase` | it conflicts with `dev`; the prover rebases |
| `fm:approved` | the reviewer approved; the merger takes it from here |
| `fm:human-ok` | the maintainer looked; the merger may merge without holding it |
| Issue #38 "formalmind ledger" | one comment per run with its cost; the planner's digests; pause notes |
| Issue #55 "Swarm notebook" | one task-list comment per run, crossed out as the work happens |
| Issue #53 "Chief updates" | the chief's daily update to the maintainer |

## Who does what

- **planner** scopes. Reads the roadmap, the changelog and the open work; writes small,
  disjoint issues; re-scopes blocked ones or asks the human; posts a digest on the ledger.
- **prover** implements. One issue at a time, on its own branch, committing and pushing as
  it goes so a cut-off run loses nothing. Opens the PR when `lake build` is clean, with a
  changelog entry. Also revises PRs that were bounced.
- **reviewer** is the first pair of eyes. Reads the issue and the whole diff, leaves inline
  comments with suggestions, approves or bounces. No toolchain; the build is checked later.
- **merger** is the second pair of eyes and the one who merges. The workflow first runs
  `lake build` and the `sorry` check on the exact head. Then the merger reads the diff
  fresh, verifies every claim made in the thread against the code (a theorem the prover
  says it proved must exist without `sorry`; a suggestion the reviewer says was applied must
  be in the diff; a remark about code that is not there is called out as a hallucination),
  decides whether a human must see it (theorem statements or recorded decisions changed,
  wide diffs, many rounds, or a false claim), and then squash-merges, bounces, or holds
  the PR for `@mmsaki`.
- **chief** runs once a day at 23:40 UTC, before the budget resets, and posts one comment
  on the pinned issue #53 "Chief updates", tagging the maintainer. Its first line is one
  of **Done**, **Working**, **Waiting on you** or **Paused on budget**, followed by what
  landed, what is in flight, what needs the maintainer, and the spend. Following that
  issue is how you know whether the swarm is finished.
- **the human** is tagged only when a decision is needed. `fm:human-ok` on a PR tells the
  merger the maintainer has looked and it may merge as is.
- **dispatcher** is not a model. Every 30 minutes, or as soon as an `fm:` label changes, it
  sums the ledger, and if the budget allows picks one job in this order: merge, review,
  revise, resume, new issue, plan.

## Notebook

Every role keeps a notebook: one comment per run on the pinned issue #55 "Swarm notebook",
written as a task list that gets crossed out as the work happens. The chief reads the
day's notes in the evening and checks them against what is actually on `dev`.

1. **Open the note first**, before any real work, with
   `gh api repos/$REPO/issues/$NOTEBOOK_ISSUE/comments -F body=@note.md --jq .id` and keep
   the returned comment id. `note.md` is:

   ```markdown
   <!-- fm-note role=<role> ref=#<n> run=<RUN_ID> -->
   **<role>** #<n> — <one line: what this run is for>
   - [ ] <task>
   - [ ] <task>
   ```

   Tasks are the concrete steps you intend to take, three to eight of them, in order.
2. **Cross out as you go.** After each task, rewrite the comment with
   `gh api -X PATCH repos/$REPO/issues/comments/<id> -F body=@note.md`: `- [x]` for done,
   `- [ ] ~~task~~ dropped: <why>` for abandoned, and new lines for tasks you discovered.
   Never delete a task; the history of the list is the point.
3. **Close the note** with two more lines under the list before you post your final
   comment on the issue or PR:
   `**Verified:**` facts the chief can check, each one concrete (a theorem name and file,
   a PR number and label, a build result);
   `**Left:**` what is unfinished, doubtful, or for someone else. "Nothing" is fine.

Unticked boxes at the end of a run mean unfinished work, and that is useful information,
not a failure. A claim in **Verified** that the chief cannot confirm on `dev` is a failure.

## Budget

`$2.00` a day and `$50.00` a month, enforced by the dispatcher from the ledger. Each role
runs under its own cap (`--max-budget-usd`): plan, review and merge `$0.40`, prove `$1.20`.
A run that gets cut off is charged its whole cap. When the budget is spent the dispatcher
posts one pause note on the ledger and waits for the reset (UTC midnight, first of the month).

## Safety rails

- Only one model job per sweep, and sweeps never overlap.
- A prover gets at most two runs per issue per day before the issue is parked as `fm:blocked`.
- The reviewer bounces a PR at most twice before parking it.
- Nothing is merged without a clean build on the exact head, and never with `sorry`,
  `admit` or a new axiom.
- Roles can only hand off forward: planner to prover, prover to reviewer, reviewer and
  merger back to prover or to the human. Nobody tags the planner.

## Driving it by hand

`gh workflow run formalmind-swarm.yml -f role=plan` plans now; `-f role=prove -f number=12`
starts or resumes issue 12; `-f role=review -f number=40` or `-f role=merge -f number=40`
act on PR 40. Labelling by hand works too: put `fm:todo` on any issue to queue it, or
`fm:approved` on any PR to send it to the merger.
