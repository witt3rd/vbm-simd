#!/usr/bin/env bash
# Repository lints (Tier 1): shell files parse; scripts are executable; the repository stays free of internal names and local paths (it is public); no tab or
# trailing-space damage is checked here. The detector has a negative self-test (it must flag a planted internal name and a planted local path).
set -euo pipefail
export LC_ALL=C
cd "$(dirname "$0")/.."
bad=0
fail() { echo "lint: $*" >&2; bad=1; }
# the deny pattern is written so that this file does not match itself
deny='(first''mate|rog''er|mcfee''ly|sp''ire|ja''nus|/hom''e/|c''aptain|\bk''ing\b|\bpr''ince\b)'
scan_names() { local f; for f in "$@"; do [ -f "$f" ] && [ "$f" != LICENSE ] || continue; if grep -nEi -- "$deny" "$f" >/dev/null 2>&1; then echo "$f: $(grep -nEi -- "$deny" "$f" | sed -n 1,2p | tr '\n' ' ')"; fi; done; }
t=$(mktemp); trap 'rm -f "$t"' EXIT
printf 'see the %s box\n' "ca""ptain" > "$t"; [ -n "$(scan_names "$t")" ] || { echo "lint: self-test: an internal name is not flagged" >&2; exit 1; }
printf 'path /ho''me/x\n' > "$t"; [ -n "$(scan_names "$t")" ] || { echo "lint: self-test: a local path is not flagged" >&2; exit 1; }
printf 'a plain line\n' > "$t"; [ -z "$(scan_names "$t")" ] || { echo "lint: self-test: a clean line is flagged" >&2; exit 1; }
files=$(git ls-files --cached --others --exclude-standard)
for f in $files; do
  [ -f "$f" ] || continue
  first=$(sed -n 1p "$f" 2>/dev/null || true)
  if [[ $first == '#!'*bash* || $first == '#!'*sh ]]; then bash -n "$f" || fail "$f does not parse"; fi
  case $f in scripts/land/*) ;; scripts/*.sh|scripts/*.py|scripts/land-direct) [ -x "$f" ] || fail "$f is not executable";; esac
done
names=$(scan_names $files); [ -z "$names" ] || fail "internal names or local paths: $names"
[ "$bad" = 0 ] && echo "lint: ok (shell parses, scripts executable, no internal names)"
exit "$bad"
