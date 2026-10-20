# The formalmind swarm

The swarm's role docs are skills now, in the `formalmind` plugin:
[formalmind/skills](https://github.com/formalmind/skills). Start with
[`swarm`](https://github.com/formalmind/skills/blob/main/plugins/formalmind/skills/swarm/SKILL.md),
the shared rules every role reads first.

This repository is the swarm's home. What stays here:

- `.github/workflows/formalmind-*.yml` and `formal-mind.yml`: the dispatcher and the bots.
  Each one checks out `formalmind/skills` at the commit in the repository variable
  `FORMALMIND_SKILLS_REF` and installs the plugin from it.
- `projects.json`: every proofs repository the swarm works in, with the protocol it models.
- `project-setup.sh`, `project-sync.sh`: the GitHub Project board that mirrors the `fm:` labels.

To change a role, edit its skill in `formalmind/skills`, merge, then
`gh variable set FORMALMIND_SKILLS_REF -b <sha>` here.
