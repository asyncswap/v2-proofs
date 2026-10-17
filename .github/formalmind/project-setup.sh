#!/usr/bin/env bash
# One-time setup of the swarm's GitHub Project: the Status options match the Kanban in the
# Formal Mind app, "Roadmap item" lists the README's numbered Roadmap, and Start/Target date
# feed the Roadmap layout. Prints the project number to store as the FORMALMIND_PROJECT
# repository variable. Re-running it on an existing project only fills in what is missing.
#
# Usage: project-setup.sh [owner/repo] [title]
# Needs: gh with the `project` scope (gh auth refresh -s project)
set -euo pipefail

REPO="${1:-asyncswap/v2-proofs}"
TITLE="${2:-Formal Mind swarm}"
OWNER="${REPO%%/*}"

number="$(gh project list --owner "$OWNER" --format json --limit 100 --jq ".projects[] | select(.title == \"$TITLE\") | .number" | head -1)"
if [ -z "$number" ]; then
	number="$(gh project create --owner "$OWNER" --title "$TITLE" --format json --jq .number)"
	echo "Created project #$number"
fi
project_id="$(gh project view "$number" --owner "$OWNER" --format json --jq .id)"
gh project link "$number" --owner "$OWNER" --repo "$REPO" >/dev/null 2>&1 || true
gh project edit "$number" --owner "$OWNER" --description "Mirrors the formalmind swarm's fm: labels on $REPO, one to one with the Kanban in the Formal Mind app." >/dev/null

fields="$(gh project field-list "$number" --owner "$OWNER" --format json --limit 50)"
has_field() { jq -e --arg n "$1" '.fields[] | select(.name == $n)' <<<"$fields" >/dev/null; }

# Status: replace GitHub's default Todo / In Progress / Done with the swarm's columns.
status_id="$(jq -r '.fields[] | select(.name == "Status") | .id' <<<"$fields")"
gh api graphql -f query='
	mutation($field: ID!) {
		updateProjectV2Field(input: {
			fieldId: $field
			singleSelectOptions: [
				{ name: "Todo",        color: GRAY,   description: "Queued with fm:todo for a prover" }
				{ name: "In progress", color: YELLOW, description: "A prover is on it, or it went back for changes" }
				{ name: "In review",   color: BLUE,   description: "Open PRs waiting for the reviewer" }
				{ name: "Approved",    color: GREEN,  description: "Reviewed; the merger checks and merges" }
				{ name: "Blocked",     color: RED,    description: "Waiting on a human decision" }
				{ name: "Done",        color: PURPLE, description: "Merged or closed as completed" }
			]
		}) { projectV2Field { ... on ProjectV2SingleSelectField { name } } }
	}' -f field="$status_id" >/dev/null
echo "Status options set"

if ! has_field "Roadmap item"; then
	readme="$(gh api "repos/$REPO/contents/README.md?ref=dev" --jq .content | base64 --decode)"
	options="$(awk '/^## Roadmap/{on=1; next} /^## /{on=0} on' <<<"$readme" \
		| grep -E '^[0-9]+\. ' \
		| sed -E 's/^([0-9]+)\. (~~)?\*\*([^*]+)\*\*.*/\1. \3/' \
		| paste -sd, -)"
	gh project field-create "$number" --owner "$OWNER" --name "Roadmap item" --data-type SINGLE_SELECT --single-select-options "$options" >/dev/null
	echo "Roadmap item options: $options"
fi
has_field "Start date" || gh project field-create "$number" --owner "$OWNER" --name "Start date" --data-type DATE >/dev/null
has_field "Target date" || gh project field-create "$number" --owner "$OWNER" --name "Target date" --data-type DATE >/dev/null

echo "Project number: $number"
echo "Next: gh variable set FORMALMIND_PROJECT --repo $REPO --body $number"
