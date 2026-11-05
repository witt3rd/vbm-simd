#!/usr/bin/env bash
# Lint: no tooling runs a declared long runner (scripts/long-runners.txt) outside scripts/run-scoped.sh. An aborted whole-shim mutation run once left orphans
# (parent pid 1) for hours; every long runner is run under a transient scope with a bound (scripts/run-scoped.sh), reaped on exit.
# Two kinds of entry: `NAME` (callers must wrap) and `self NAME` (the runner's own file must carry the guard that re-execs it under the helper).
# A line RUNS a `NAME` runner when the name is at command position (line start, after ; & | ( $( -- python3 bash sh time); it is allowed when `run-scoped.sh` appears earlier on that line.
# Comments and mentions inside strings are not runs. --selftest (Tier 1 runs it): a direct call, a mise/python3/bash-prefixed call and a pipeline call each FAIL; a scoped call passes;
# a `self` runner without the guard FAILS and one with it passes.
# LIMIT (stated, accepted): this is a guard against accidents, not against a determined subject. Evasion by indirection (a variable holding the runner, a bash -c string, a renamed copy) is not detected.
set -euo pipefail
cd "$(dirname "$0")/.."
entries=$(grep -vE '^[[:space:]]*(#|$)' scripts/long-runners.txt || true)
[ -n "$entries" ] || { echo "lint-scoped-runners: scripts/long-runners.txt lists no runner" >&2; exit 1; }
runners=$(grep -vE '^self ' <<<"$entries" | paste -sd'|' | sed 's/\./\\./g' || true)
selfs=$(sed -n 's/^self //p' <<<"$entries")
pre='(^|[;&|(]|\$\(|--|[[:space:]](python3?|bash|sh|exec|time|nice|env))[[:space:]]*(python3?[[:space:]]+|bash[[:space:]]+|sh[[:space:]]+)?(\./)?(scripts/)?'
run_re="${pre}(${runners:-NO_SUCH_RUNNER})([[:space:];&|)]|\$)"
scan() { grep -HnE "$run_re" "$@" | grep -vE '^[^:]+:[0-9]+:[[:space:]]*#' | grep -vE 'run-scoped\.sh.*('"${runners:-NO_SUCH_RUNNER}"')' || true; }
guard_ok() { local c; c=$(grep -vE '^[[:space:]]*#' "$1" || true); grep -qE 'RUN_SCOPED_INNER.*exec[[:space:]]+(\./)?(scripts/)?run-scoped\.sh' <<<"$c"; }
t=$(mktemp); trap 'rm -f "$t"' EXIT
# the fixtures name a sample runner, mutants.py, and are judged against that name whatever the list says
for bad in 'python3 scripts/mutants.py --jobs 4' 'mise exec -- scripts/mutants.py' 'x=$(python3 scripts/mutants.py)' 'cd d && ./mutants.py' 'true; bash scripts/mutants.py' 'run | scripts/mutants.py' 'mutants.py --list'; do
  printf '%s\n' "$bad" > "$t"
  [ -n "$(grep -HnE "${pre}(mutants\.py)([[:space:];&|)]|\$)" "$t" || true)" ] || { echo "lint-scoped-runners: self-test: did not flag: $bad" >&2; exit 1; }
done
for ok in 'scripts/run-scoped.sh mutants 3600 python3 scripts/mutants.py --jobs 4' '# python3 scripts/mutants.py is the runner' 'echo "see mutants.py"' 'TIER2_ONLY="scripts/mutants.py"' 'cat scripts/mutants.py'; do
  printf '%s\n' "$ok" > "$t"
  [ -z "$(grep -HnE "${pre}(mutants\.py)([[:space:];&|)]|\$)" "$t" | grep -vE '^[^:]+:[0-9]+:[[:space:]]*#' | grep -vE 'run-scoped\.sh.*mutants\.py' || true)" ] || { echo "lint-scoped-runners: self-test: flagged a good line: $ok" >&2; exit 1; }
done
printf '%s\n' '#!/usr/bin/env bash' 'set -e' > "$t"; ! guard_ok "$t" || { echo "lint-scoped-runners: self-test: a self runner with no guard passed" >&2; exit 1; }
printf '%s\n' '# RUN_SCOPED_INNER=1 exec scripts/run-scoped.sh only in a comment' > "$t"; ! guard_ok "$t" || { echo "lint-scoped-runners: self-test: a commented guard passed" >&2; exit 1; }
printf '%s\n' '[ -n "${RUN_SCOPED_INNER:-}" ] || RUN_SCOPED_INNER=1 exec scripts/run-scoped.sh x 60 "$0" "$@"' > "$t"; guard_ok "$t" || { echo "lint-scoped-runners: self-test: a guarded self runner was refused" >&2; exit 1; }
[ "${1:-}" != --selftest ] || echo "lint-scoped-runners: self-tests ok"
bad=""
for r in $selfs; do
  f=$(git ls-files | grep -E "(^|/)$r\$" | head -1 || true)
  [ -n "$f" ] || { echo "lint-scoped-runners: the self runner $r is not in the tree" >&2; exit 1; }
  guard_ok "$f" || bad="$bad$f: no RUN_SCOPED_INNER guard that re-execs it under scripts/run-scoped.sh"$'\n'
done
files=$(git ls-files 'scripts/*.sh' scripts/wt scripts/land-direct 'scripts/githooks/*' '.github/workflows/*' | grep -vE '^scripts/(lint-scoped-runners|run-scoped)\.sh$' || true)
if [ -n "$runners" ]; then
  # shellcheck disable=SC2086
  bad="$bad$(scan $files)"
fi
[ -z "$bad" ] || { echo "tier1: a long runner runs outside scripts/run-scoped.sh (scripts/long-runners.txt):" >&2; echo "$bad" >&2; exit 1; }
echo "lint-scoped-runners: ok"
