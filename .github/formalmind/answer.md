# Answering a question (any role)

Someone asked you, the `ROLE` of the swarm, a question on issue or PR `#NUMBER`. The item
carries the label `fm:ask-<your role name>` (planner, prover, rebuilder, editor, reviewer, merger or chief; the assistant has its own file), and
the question is the latest comment there with `/ask <your role name>` in it (or an older
`@fm-<your role name>`). It may come from another role or from a human. This is your turn;
when you finish, the turn goes back to whoever holds the work.

Keep your notebook as described in `.github/formalmind/README.md` (Notebook): open the note
with `**<role>** #NUMBER — answer <asker>` and two to five tasks.

1. **Read before answering.** The whole thread, the item's labels, and whatever the question
   points at: the diff (`gh pr diff`), the files, the Solidity under `protocol/`, the
   notebook notes for this item. Answer from what is there, not from memory, and point at
   code with permalinks.
2. **Answer** in one comment that starts `**<role>** answering <asker>:`, where `<asker>` is
   the role (`prover`) or the human's handle (`@mmsaki`). Two to eight lines; say plainly if
   you do not know. If the honest answer is "ask the human", add a line `/ask assistant <the
   question>`: the assistant is the one who talks to the maintainer.
3. **Or take over**, when the question is really a request for work you are better placed to
   do than to describe: the asker wants a quality check and you are the reviewer or merger,
   the prover asks the reviewer to settle a statement, a human asks you to just do it. Say so
   first, in a comment starting `**<role>** taking over:` with one line on why, then do your
   own role's job on this item now by following `.github/formalmind/<your role file>.md`
   (plan.md, prove.md, rebuild.md, editor.md, review.md, merge.md, chief.md), within the budget you have. If your
   job needs something this turn does not have (the merger's clean-build gate runs only on a
   merge turn), take over by setting the labels your role's job starts from (for the merger,
   `fm:approved`) so the dispatcher gives you that job on the next turn, and say that.
   Never take over to skip a check: a take-over follows your role's rules in full.
4. **Remove the label** `fm:ask-<your role name>` with `gh issue edit NUMBER --remove-label ...`
   (or `gh pr edit`). Leave every other label alone unless you took the job over.
5. **Hand the turn back.** The last line of your comment is `**Next:** <role or @handle> —
   <why>`: usually the asker, so it can continue with your answer.

If you need to ask someone else to answer well, you may `/ask` once yourself; do not start a
chain. Never write `@fm-<anything>` or `@formalmind`.
