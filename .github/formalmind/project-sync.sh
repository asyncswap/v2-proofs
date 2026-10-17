#!/usr/bin/env bash
# Mirror issues and PRs onto the swarm's GitHub Project, one to one with the Kanban in the
# Formal Mind app. Status comes from the fm: labels with the same rules the app uses:
#
#   closed (merged PR / completed issue)   -> Done
#   fm:blocked                             -> Blocked
#   fm:approved                            -> Approved
#   fm:in-progress | fm:changes | fm:needs-rebase -> In progress
#   any other open PR                      -> In review
#   fm:todo                                -> Todo
#   anything else open                     -> no Status
#
# Closed-unmerged PRs and issues closed as not planned leave the project. The swarm's own
# ledger, notebook and chief issues are never added. "Roadmap item" follows "roadmap item N"
# in the title or body; "Start date" / "Target date" are opened / merged-or-closed, so the
# project's Roadmap layout draws the same bars as the app.
#
# Usage: project-sync.sh <number>...   sync these issues/PRs
#        project-sync.sh --all         sync every issue and PR
# Env:   GH_TOKEN (Projects read/write on the org), GITHUB_REPOSITORY, PROJECT_NUMBER
set -euo pipefail

OWNER="${GITHUB_REPOSITORY%%/*}"
REPO="$GITHUB_REPOSITORY"
PINNED=" ${PINNED_ISSUES:-38 53 55} "

fields="$(gh project field-list "$PROJECT_NUMBER" --owner "$OWNER" --format json --limit 50)"
project_id="$(gh project view "$PROJECT_NUMBER" --owner "$OWNER" --format json --jq .id)"
field_id() { jq -r --arg n "$1" '.fields[] | select(.name == $n) | .id' <<<"$fields"; }
option_id() { jq -r --arg f "$1" --arg o "$2" '.fields[] | select(.name == $f) | .options[]? | select(.name == $o or (.name | startswith($o + ". "))) | .id' <<<"$fields"; }
STATUS_FIELD="$(field_id Status)"
ROADMAP_FIELD="$(field_id "Roadmap item")"
START_FIELD="$(field_id "Start date")"
TARGET_FIELD="$(field_id "Target date")"

status_of() { # $1 = issue JSON from the REST API
	jq -r '
		[.labels[].name] as $l
		| if .state == "closed" then "Done"
		  elif ($l | index("fm:blocked")) then "Blocked"
		  elif ($l | index("fm:approved")) then "Approved"
		  elif ($l | index("fm:in-progress")) or ($l | index("fm:changes")) or ($l | index("fm:needs-rebase")) then "In progress"
		  elif .pull_request then "In review"
		  elif ($l | index("fm:todo")) then "Todo"
		  else "" end' <<<"$1"
}

set_select() { # item field option-name ; clears the field when the option is empty
	[ -n "$2" ] || return 0
	if [ -z "$3" ]; then
		gh project item-edit --id "$1" --project-id "$project_id" --field-id "$2" --clear >/dev/null
	else
		local opt; opt="$(option_id "$(jq -r --arg id "$2" '.fields[] | select(.id == $id) | .name' <<<"$fields")" "$3")"
		[ -n "$opt" ] && gh project item-edit --id "$1" --project-id "$project_id" --field-id "$2" --single-select-option-id "$opt" >/dev/null
	fi
}

set_date() { # item field ISO-timestamp
	[ -n "$2" ] && [ -n "$3" ] && gh project item-edit --id "$1" --project-id "$project_id" --field-id "$2" --date "${3:0:10}" >/dev/null
	return 0
}

sync_one() {
	local number="$1" issue url state status merged reason item roadmap
	case "$PINNED" in *" $number "*) return 0 ;; esac
	issue="$(gh api "repos/$REPO/issues/$number")"
	url="$(jq -r .html_url <<<"$issue")"
	state="$(jq -r .state <<<"$issue")"
	merged="$(jq -r '.pull_request.merged_at // empty' <<<"$issue")"
	reason="$(jq -r '.state_reason // empty' <<<"$issue")"

	if [ "$state" = closed ] && { { jq -e .pull_request >/dev/null <<<"$issue" && [ -z "$merged" ]; } || [ "$reason" = not_planned ]; }; then
		item="$(gh project item-list "$PROJECT_NUMBER" --owner "$OWNER" --format json --limit 500 --jq ".items[] | select(.content.url == \"$url\") | .id")"
		[ -n "$item" ] && gh project item-delete "$PROJECT_NUMBER" --owner "$OWNER" --id "$item" >/dev/null && echo "#$number removed (closed without merging)"
		return 0
	fi

	item="$(gh project item-add "$PROJECT_NUMBER" --owner "$OWNER" --url "$url" --format json --jq .id)"
	status="$(status_of "$issue")"
	set_select "$item" "$STATUS_FIELD" "$status"
	roadmap="$(jq -r '"\(.title)\n\(.body // "")"' <<<"$issue" | grep -oiE 'roadmap item [0-9]+' | head -1 | grep -oE '[0-9]+' || true)"
	[ -n "$roadmap" ] && set_select "$item" "$ROADMAP_FIELD" "$roadmap"
	set_date "$item" "$START_FIELD" "$(jq -r .created_at <<<"$issue")"
	set_date "$item" "$TARGET_FIELD" "${merged:-$(jq -r '.closed_at // empty' <<<"$issue")}"
	echo "#$number -> ${status:-No Status}${roadmap:+ (roadmap $roadmap)}"
}

if [ "${1:-}" = --all ]; then
	set -- $(gh api --paginate "repos/$REPO/issues?state=all&per_page=100" --jq '.[].number')
fi
for n in "$@"; do sync_one "$n"; done
