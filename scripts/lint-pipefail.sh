#!/usr/bin/env bash
# Lint: under `set -o pipefail` a producer piped into an early-exiting consumer (`grep -q`, `grep -m`, `head`) can die of SIGPIPE
# (exit 141) when the consumer leaves before the producer finishes writing: a flaky gate. Capture then test (`grep -q p <<<"$x"`),
# or let the consumer drain the pipe (`| grep p >/dev/null`, `| sed -n 1p`). A line that needs the exception says `# pipefail-ok`.
set -euo pipefail
cd "$(dirname "$0")/.."
bad_re='\|[[:space:]]*(grep[[:space:]]+(-[A-Za-z]*[qm][A-Za-z0-9]*|--quiet|--max-count)([[:space:]]|=)|head([[:space:]]|$))'
scan() { grep -nE "$bad_re" "$@" | grep -v 'pipefail-ok' || true; }
# negative self-test: the detector must flag each known-bad shape and pass each good one
t=$(mktemp); trap 'rm -f "$t"' EXIT
for bad in 'echo "$x" | grep -q foo' 'cmd | grep -qE x' 'cmd | head -1' 'cmd | grep -m1 x' 'a | grep --quiet x'; do
  printf '%s\n' "$bad" > "$t"; [ -n "$(scan "$t")" ] || { echo "lint-pipefail: self-test: did not flag: $bad" >&2; exit 1; }
done
for ok in 'grep -q foo <<<"$x"' 'cmd | grep foo >/dev/null' 'cmd | sed -n 1p' 'cmd | head -1 # pipefail-ok' 'x | grep -c y'; do
  printf '%s\n' "$ok" > "$t"; [ -z "$(scan "$t")" ] || { echo "lint-pipefail: self-test: flagged a good line: $ok" >&2; exit 1; }
done
files=$(git ls-files --cached --others --exclude-standard 'scripts/*.sh' | grep -v '^scripts/lint-pipefail.sh$' || true)
# shellcheck disable=SC2086
hits=$(scan $files)
[ -z "$hits" ] || { echo "tier1: pipefail-unsafe pipelines (producer | early-exiting consumer):" >&2; echo "$hits" >&2; exit 1; }
echo "lint-pipefail: ok"
