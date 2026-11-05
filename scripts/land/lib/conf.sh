#!/usr/bin/env bash
# The per-repository configuration (default scripts/land.conf), read by bin/land-direct and bin/land-red. Sourced, never run.
#
# The file is DATA, not code: one `LAND_KEY=value` per line, `#` starts a comment line, a value may be wrapped in one pair of single or double
# quotes, nothing is ever expanded or executed while reading it, and an unknown key is an error (a typo must not silently turn a gate off).
# The values that name commands (LAND_GATES_CMD, LAND_TEST_CMD, ...) are run later, by the lander, with `bash -c` inside the scratch worktree.
#
# The keys and their defaults are the stable interface of this tool (README, "Configuration"): conf_defaults sets them, conf_parse reads a file.
land_conf_keys="LAND_BASE LAND_REMOTE LAND_CI_WORKFLOW LAND_TIER1_JOB LAND_RED_MODE LAND_RED_WAIT LAND_GATES_CMD LAND_TEST_CMD LAND_REGEN_CMD LAND_GEN_CMD
 LAND_GENERATED_LIST LAND_PROD_PATHS LAND_BUDGET_LINES LAND_REQUIRE_TRAILERS LAND_CONVENTIONAL LAND_COMMIT_TYPES LAND_PROTECTED LAND_FIX_PATHS
 LAND_KNOWN_FLAKY LAND_FLAKY_RERUN_WAIT LAND_TIER2_JOB LAND_HOOKS_DIR LAND_AUTO_UPDATE LAND_LOCALE LAND_LOCK_WAIT LAND_TIER1_TIMEOUT LAND_STEP_TIMEOUT LAND_GIT_TIMEOUT"

conf_defaults() {
  LAND_BASE=main; LAND_REMOTE=origin            # the branch landed on, and the remote that holds it
  LAND_CI_WORKFLOW=ci.yml; LAND_TIER1_JOB=tier1 # what the red check reads: the Tier 1 job of this workflow's latest push run
  LAND_RED_MODE=push; LAND_RED_WAIT=60          # push | push+dispatch | off ; seconds to wait for a Tier 1 that is still running
  LAND_GATES_CMD=; LAND_TEST_CMD=               # Tier 1 = the gates command, then the test command, on the rebased combination (at least one is required)
  LAND_REGEN_CMD=; LAND_GEN_CMD=                # regenerate generated files: after a conflict in them / always after the rebase
  LAND_GENERATED_LIST=                          # path (in the repository) of a file listing generated paths, one per line, `#` comments
  LAND_PROD_PATHS=; LAND_BUDGET_LINES=150       # production paths counted by the size budget (empty: no budget); a `Diff-Budget:` trailer waives it
  LAND_REQUIRE_TRAILERS=                        # trailer names every commit must carry, space separated (e.g. Task-ID)
  LAND_CONVENTIONAL=1                           # require `type(scope): summary` (or git's own `Revert "..."`)
  LAND_COMMIT_TYPES="feat fix docs chore refactor test perf build ci style revert"
  LAND_PROTECTED=; LAND_FIX_PATHS=              # shell patterns (* matches /): the protected set; the only paths a fix for a red main may touch
  LAND_KNOWN_FLAKY=; LAND_FLAKY_RERUN_WAIT=300  # path (in the repository) of the known-flaky list (`name owner YYYY-MM-DD issue`); seconds to wait for the one rerun
  LAND_TIER2_JOB=                               # the name of the Tier 2 job: a real failure of it freezes landing (24 h), a green run lifts the freeze; empty: Tier 2 is not read
  LAND_HOOKS_DIR=scripts/land.d                 # repository-owned hooks (README, "Hooks")
  LAND_AUTO_UPDATE=none                          # none | patch | minor: what the scheduled workflow may update by itself (land-update --auto); a major release never
  LAND_LOCALE=C                                 # pinned for collation, glob and sort order
  LAND_LOCK_WAIT=90; LAND_TIER1_TIMEOUT=1800; LAND_STEP_TIMEOUT=600; LAND_GIT_TIMEOUT=180   # seconds
}

# conf_parse NAME: read the file's text from stdin; NAME is only used in messages. Returns 2 (with a message) on anything it does not understand.
conf_parse() {
  local name=$1 line n=0 k v
  while IFS= read -r line || [ -n "$line" ]; do
    n=$((n + 1)); line=${line%$'\r'}
    [[ "$line" =~ ^[[:space:]]*(#.*)?$ ]] && continue
    if ! [[ "$line" =~ ^[[:space:]]*(LAND_[A-Z0-9_]+)=(.*)$ ]]; then echo "$name:$n: not a LAND_KEY=value line: $line" >&2; return 2; fi
    k=${BASH_REMATCH[1]}; v=${BASH_REMATCH[2]}
    case " $(echo $land_conf_keys) " in *" $k "*) ;; *) echo "$name:$n: unknown key $k (a typo would silently turn a gate off)" >&2; return 2;; esac
    v=${v%"${v##*[![:space:]]}"}
    if [[ "$v" =~ ^\"(.*)\"$ ]] || [[ "$v" =~ ^\'(.*)\'$ ]]; then v=${BASH_REMATCH[1]}; fi
    printf -v "$k" '%s' "$v"
  done
  return 0
}

# conf_validate: the values the tool relies on must be well formed. Returns 2 with a message otherwise.
conf_validate() {
  local bad= k; b() { [ -n "$bad" ] || bad=$1; }
  case $LAND_RED_MODE in push|push+dispatch|off) ;; *) b "LAND_RED_MODE must be push, push+dispatch or off (is '$LAND_RED_MODE')";; esac
  [[ "$LAND_BASE" =~ ^[A-Za-z0-9._/-]+$ ]] || b "LAND_BASE is not a branch name ('$LAND_BASE')"
  [[ "$LAND_REMOTE" =~ ^[A-Za-z0-9._/-]+$ ]] || b "LAND_REMOTE is not a remote name ('$LAND_REMOTE')"
  for k in LAND_BUDGET_LINES LAND_FLAKY_RERUN_WAIT LAND_RED_WAIT LAND_LOCK_WAIT LAND_TIER1_TIMEOUT LAND_STEP_TIMEOUT LAND_GIT_TIMEOUT; do
    [[ "${!k}" =~ ^[0-9]+$ ]] || b "$k must be a whole number (is '${!k}')"
  done
  case $LAND_AUTO_UPDATE in none|patch|minor) ;; *) b "LAND_AUTO_UPDATE must be none, patch or minor (is '$LAND_AUTO_UPDATE'; a major release is never automatic)";; esac
  [[ "$LAND_REQUIRE_TRAILERS" =~ ^[A-Za-z0-9\ -]*$ ]] || b "LAND_REQUIRE_TRAILERS: trailer names are letters, digits and - separated by spaces"
  [ -n "$LAND_GATES_CMD$LAND_TEST_CMD" ] || b "neither LAND_GATES_CMD nor LAND_TEST_CMD is set: there is no Tier 1, so nothing could gate a landing"
  [ -z "$bad" ] || { echo "land.conf: $bad" >&2; return 2; }
}
