# The formalmind swarm

A small team of bots that owns the Lean specification in this repository and keeps working
on the roadmap in `README.md`, hands off, within a spend budget. All of them post as
**formalmind[bot]**; the bold word at the start of a comment says which role is talking.
The roles take **turns**, one at a time: each turn ends by naming who goes next, and any
role (or human) can stop to ask another role a question with `/ask <role>`. Humans are
tagged as `@mmsaki` when a decision is needed. Nobody writes `@fm-<role>` (those handles are
not ours, and `@fm-chief` is a stranger's account) or `@formalmind` (that summons the chat
bot, which is a different workflow).

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
| `fm:ask-<role>` | someone asked that role a question here; it answers on its next turn |
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
  sums the ledger, and if the budget allows gives the turn to one job in this order:
  answer a question, merge, review, revise, resume, new issue, plan.

## Turns, questions and take-overs

Exactly one role holds the turn at a time (the workflow never runs two). A turn ends in one
of three ways, and every final comment says which in its last line:

- **Hand over.** `**Next:** <role> — <why>` (or `**Next:** @mmsaki — <the decision>`, or
  `**Next:** nobody — <why the work is finished>`). The labels you set are what actually
  route the work; the Next line is the human-readable baton, and the board shows it.
- **Ask for help.** When you cannot finish well without another role's judgement, ask
  instead of guessing: comment on the issue or PR

  ```markdown
  **prover** /ask reviewer Is `step_bal_nonneg` the statement you would review against, or
  should it quantify over every entry point? I'll hold the PR until you answer.
  ```

  and end your turn (keep your job label; you resume after the answer). The `/ask` line adds
  `fm:ask-reviewer`, and the dispatcher gives the reviewer the next turn, before anything else.
  Humans ask the same way: `/ask chief how are we doing?` on any issue or PR.
- **Answer or take over.** A role woken by `fm:ask-<role>` reads `answer.md` instead of its
  usual instructions: it answers in one comment and removes the label, and the work goes
  back to whoever holds it. When the question is really "can you check this?" and the
  asked role is the better one to do it (the reviewer as the quality check, say), it may
  **take over** the job: it says so, does its own role's work on the item in that same turn,
  and moves the labels as its role would. An agent in the loop, the same way a human is.

## One rule for every `gh api` call

Write the path first and every flag after it: `gh api repos/$REPO/... -X PATCH -F body=@file`.
The tool allowlist matches commands word by word, so `gh api` must be the first two words;
a command that starts with `gh api -X ...` or `gh api --paginate ...` is refused and your
run silently loses that step. Only call paths under `repos/$REPO/`.

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
   `gh api repos/$REPO/issues/comments/<id> -X PATCH -F body=@note.md`: `- [x]` for done,
   `- [ ] ~~task~~ dropped: <why>` for abandoned, and new lines for tasks you discovered.
   Never delete a task; the history of the list is the point.
3. **Close the note** with two more lines under the list before you post your final
   comment on the issue or PR:
   `**Verified:**` facts the chief can check, each one concrete (a theorem name and file,
   a PR number and label, a build result);
   `**Left:**` what is unfinished, doubtful, or for someone else. "Nothing" is fine;
   `**Next:**` the same hand-over line as your final comment (see Turns).

Unticked boxes at the end of a run mean unfinished work, and that is useful information,
not a failure. A claim in **Verified** that the chief cannot confirm on `dev` is a failure.

## Budget

`$5.00` a day and `$150.00` a month, enforced by the dispatcher from the ledger. Each role
runs under its own cap (`--max-budget-usd`): plan, review and merge `$0.40`, prove `$1.20`.
Answering a question costs the asked role's own cap, since it may take the job over.
Within its turn a role may take up to 200 model steps (`TURNS_<ROLE>` in the workflow, set
per role); the dollar cap is what normally ends a run, the step limit is only the ceiling.
A run that gets cut off is charged its whole cap. When the budget is spent the dispatcher
posts one pause note on the ledger and waits for the reset (UTC midnight, first of the month).

## Safety rails

- Only one model job per sweep, and sweeps never overlap.
- A prover gets at most two runs per issue per day before the issue is parked as `fm:blocked`.
- The reviewer bounces a PR at most twice before parking it.
- Nothing is merged without a clean build on the exact head, and never with `sorry`,
  `admit` or a new axiom.
- Work only moves forward through the labels: planner to prover, prover to reviewer,
  reviewer and merger back to prover or to the human. Questions can go to any role.
- At most three `/ask` answers per item per day; after that the dispatcher parks the item as
  `fm:blocked` for the human, so two roles cannot talk in circles.

## Driving it by hand

`gh workflow run formalmind-swarm.yml -f role=plan` plans now; `-f role=prove -f number=12`
starts or resumes issue 12; `-f role=review -f number=40` or `-f role=merge -f number=40`
act on PR 40. Labelling by hand works too: put `fm:todo` on any issue to queue it, or
`fm:approved` on any PR to send it to the merger. To talk to a role, comment
`/ask <role> <question>` on any issue or PR; it answers on the next turn.

## The project board

The labels are the state, and a GitHub Project mirrors them one to one, so the board on
GitHub and the Kanban in the Formal Mind app always agree. `formalmind-project.yml` sets each
item's **Status** on every label, open and close event (and sweeps hourly) with the same rules
as the app: closed is Done; then `fm:blocked`, `fm:approved`, `fm:in-progress`/`fm:changes`/
`fm:needs-rebase` (In progress); any other open PR is In review; `fm:todo` is Todo; anything
else has no Status. **Roadmap item** follows "roadmap item N" in the title or body, and Start
and Target date are opened and merged, so the project's Roadmap layout draws the same bars.
Agents never touch the board directly: they move labels, and the board follows.

Setup, once: `gh auth refresh -s project`, run `.github/formalmind/project-setup.sh`, store the
number it prints with `gh variable set FORMALMIND_PROJECT`, and give the formalmind GitHub App
the organization permission **Projects: read and write**. Then run the workflow by hand to
fill the board.
