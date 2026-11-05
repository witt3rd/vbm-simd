#!/usr/bin/env bash
# Tier 1: the spec-clause gate. docs/SPEC.md lists the clauses (`| VS-n | ... |` rows). Each clause must be DEFINED (its tag `[VS-n]` appears in a doc comment under VbmSimd/, where its machine is written)
# and DISCHARGED (the tag opens the docstring of at least one theorem under VbmSimdProofs/), and every tag used in a Lean file must be a clause. The gate has a negative self-test (a clause with no
# theorem, a clause with no definition and an unknown tag must each fail it).
set -euo pipefail
export LC_ALL=C
cd "$(dirname "$0")/.."
check() {  # check <root>: prints one line per problem
  local r=$1 id
  local clauses; clauses=$(grep -oE '^\| VS-[0-9]+ \|' "$r/docs/SPEC.md" | grep -oE 'VS-[0-9]+' | sort -u || true)
  [ -n "$clauses" ] || echo "no clause in docs/SPEC.md"
  for id in $clauses; do
    grep -rqF "[$id]" "$r/VbmSimd" --include='*.lean' 2>/dev/null || echo "$id: not defined (no [$id] tag under VbmSimd/)"
    grep -rqE "^/-- .*\[$id\]" "$r/VbmSimdProofs" --include='*.lean' 2>/dev/null || echo "$id: not discharged (no theorem docstring tagged [$id] under VbmSimdProofs/)"
  done
  local used; used=$( { grep -rhoE '\[VS-[0-9]+\]' "$r/VbmSimd" "$r/VbmSimdProofs" --include='*.lean' 2>/dev/null || true; } | grep -oE 'VS-[0-9]+' | sort -u || true)
  for id in $used; do grep -qx "$id" <<<"$clauses" || echo "$id: tag used in a Lean file but not a clause of docs/SPEC.md"; done
}
out=$(check .); [ -z "$out" ] || { echo "spec-check: FAILS:" >&2; echo "$out" >&2; exit 1; }
n=$(grep -cE '^\| VS-[0-9]+ \|' docs/SPEC.md)
# negative self-tests, on a scratch copy
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mk() { rm -rf "$T/r"; mkdir -p "$T/r/docs" "$T/r/VbmSimd" "$T/r/VbmSimdProofs"
  printf '| VS-1 | a clause |\n' > "$T/r/docs/SPEC.md"; printf '/-- `[VS-1]` machine -/\ndef m := 0\n' > "$T/r/VbmSimd/A.lean"; printf '/-- `[VS-1]` the theorem -/\ntheorem t : True := trivial\n' > "$T/r/VbmSimdProofs/A.lean"; }
mk; [ -z "$(check "$T/r")" ] || { echo "spec-check: self-test: a consistent tree is flagged" >&2; exit 1; }
mk; rm "$T/r/VbmSimdProofs/A.lean"; [ -n "$(check "$T/r")" ] || { echo "spec-check: self-test: a clause with no theorem is accepted" >&2; exit 1; }
mk; rm "$T/r/VbmSimd/A.lean"; [ -n "$(check "$T/r")" ] || { echo "spec-check: self-test: a clause with no definition is accepted" >&2; exit 1; }
mk; printf '/-- `[VS-9]` stray -/\ndef x := 0\n' >> "$T/r/VbmSimd/A.lean"; [ -n "$(check "$T/r")" ] || { echo "spec-check: self-test: an unknown tag is accepted" >&2; exit 1; }
mk; printf '/-- no tag here, only a comment mentioning VS-1 -/\ntheorem t : True := trivial\n' > "$T/r/VbmSimdProofs/A.lean"; [ -n "$(check "$T/r")" ] || { echo "spec-check: self-test: an untagged theorem discharges a clause" >&2; exit 1; }
echo "spec-check: ok ($n clauses, each defined and discharged; negative self-tests ok)"
