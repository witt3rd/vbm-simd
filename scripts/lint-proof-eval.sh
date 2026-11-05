#!/usr/bin/env bash
# Lint: proofs in VbmSimdProofs/ must not be "proved by evaluation" over big data. The kernel evaluates the literal, the exported proof term
# explodes, and the independent checker (nanoda) overflows its stack (incident: docs/decisions/0003-proof-eval-lint.md). Restate through a shallow lemma instead.
# Flags, with file:line:
#   * kernel evaluation, always: `decide +kernel`, `decide (config := {kernel := true})`, `native_decide`, `decide := true` (simp/decide config);
#   * in a declaration that uses `rfl`, `decide` or `Nat.rec`: a numeric literal > NUM_MAX, a list/array literal with > LIST_MAX elements,
#     or bracket nesting deeper than DEPTH_MAX.
# Escape hatch: scripts/proof-eval-allow.txt, one tab-separated entry per line: <file> <TAB> <text of the flagged line (substring)> <TAB> <YYYY-MM-DD expiry> <TAB> <reason>.
# An entry is honoured through its expiry date and fails the lint after it. Usage: scripts/lint-proof-eval.sh [--selftest]
set -euo pipefail
cd "$(dirname "$0")/.."
# ---- the bound, in one place -------------------------------------------------------------------------------------------------------------
NUM_MAX=256     # largest numeric literal allowed next to rfl/decide/Nat.rec
LIST_MAX=256    # most elements in a list/array literal next to rfl/decide/Nat.rec
DEPTH_MAX=64    # deepest bracket nesting next to rfl/decide/Nat.rec
# -----------------------------------------------------------------------------------------------------------------------------------------
export NUM_MAX LIST_MAX DEPTH_MAX

# scan <root> <allowlist> <today>: prints one "file:line: reason" per unallowed hit; exit 0 always (the caller judges the output)
scan() {
python3 - "$@" <<'PY'
import os, re, sys
root, allow_file, today = sys.argv[1:4]
NUM, LST, DEP = (int(os.environ[k]) for k in ("NUM_MAX", "LIST_MAX", "DEPTH_MAX"))
allow = []
if os.path.exists(allow_file):
    for raw in open(allow_file, encoding="utf-8"):
        if not raw.strip() or raw.lstrip().startswith("#"): continue
        f = raw.rstrip("\n").split("\t")
        if len(f) < 4 or not re.fullmatch(r"\d{4}-\d{2}-\d{2}", f[2]) or not f[3].strip():
            print(f"{allow_file}: malformed entry (need file, text, YYYY-MM-DD, reason): {raw.strip()}"); continue
        allow.append(f[:3])
used = set()
def allowed(path, text):
    for i, (f, t, exp) in enumerate(allow):
        if f == path and t in text:
            if exp >= today: return True
            used.add(i); print(f"{path}: allowlist entry expired {exp}: {t}")
    return False
kern = re.compile(r"decide\s*\+kernel|native_decide|decide\s*:=\s*true|kernel\s*:=\s*true")
trig = re.compile(r"\b(rfl|decide|Nat\.rec)\b")
decl = re.compile(r"^(@\[|theorem|lemma|example|def|private|protected|instance|abbrev|namespace|section|end|open|set_option|/--|/-!)")
def strip(lines):  # blank out comments, keep line structure
    out, depth = [], 0
    for l in lines:
        res, i = "", 0
        while i < len(l):
            if depth: 
                j = l.find("-/", i)
                if j < 0: i = len(l)
                else: depth -= 1; i = j + 2
            elif l.startswith("/-", i): depth += 1; i += 2
            elif l.startswith("--", i): break
            else: res += l[i]; i += 1
        out.append(res)
    return out
def depth_and_lists(text):
    """(max nesting, [(max commas+1 per bracket)]) of [ ] ( ) { } over one declaration"""
    st, mx, big = [], 0, 0
    for c in text:
        if c in "[({": st.append([c, 0, False]); mx = max(mx, len(st))
        elif c in "])}" and st:
            c0, n, nonempty = st.pop(); 
            if c0 == "[": big = max(big, n + 1 if nonempty else 0)
        elif c == "," and st: st[-1][1] += 1
        elif st and not c.isspace(): st[-1][2] = True
    return mx, big
hits = []
for dp, _, fs in os.walk(os.path.join(root, "VbmSimdProofs")):
    for fn in sorted(fs):
        if not fn.endswith(".lean"): continue
        path = os.path.relpath(os.path.join(dp, fn), root)
        raw = open(os.path.join(dp, fn), encoding="utf-8").read().split("\n")
        code = strip(raw)
        for n, l in enumerate(code, 1):
            if kern.search(l) and not allowed(path, raw[n-1]): hits.append((path, n, "kernel evaluation: " + l.strip()))
        # declaration chunks: a chunk starts at a column-0 declaration keyword
        starts = [i for i, l in enumerate(code) if decl.match(l)] + [len(code)]
        for a, b in zip(starts, starts[1:]):
            chunk = code[a:b]; text = "\n".join(chunk)
            if not trig.search(text): continue
            why = None
            for k, l in enumerate(chunk):
                for m in re.finditer(r"(?<![\w.])(\d+)(?![\w.])", l):
                    if int(m.group(1)) > NUM: why = (a + k, f"numeric literal {m.group(1)} > {NUM} next to rfl/decide/Nat.rec"); break
                if why: break
            if not why:
                d, big = depth_and_lists(text)
                if big > LST: why = (a, f"list literal with {big} elements > {LST} next to rfl/decide/Nat.rec")
                elif d > DEP: why = (a, f"bracket nesting {d} > {DEP} next to rfl/decide/Nat.rec")
            if why and not allowed(path, raw[why[0]]): hits.append((path, why[0] + 1, why[1]))
for p, n, w in sorted(set(hits)): print(f"{p}:{n}: {w}")
PY
}

allow=scripts/proof-eval-allow.txt
if [ "${1:-}" != --selftest ]; then
  out=$(scan . "$allow" "$(date +%F)")
  [ -z "$out" ] || { echo "tier1: proof-by-evaluation over big data in VbmSimdProofs (restate via a shallow lemma; or allowlist with reason+expiry in $allow):" >&2; echo "$out" >&2; exit 1; }
  echo "lint-proof-eval: ok"
  exit 0
fi

# ---- negative self-tests: fixtures in a scratch tree -------------------------------------------------------------------------------------
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/VbmSimdProofs"; F=$T/VbmSimdProofs/Fix.lean
nums() { seq -s, 1 "$1"; }
chk() {  # <name> <expect: hit|clean> <lean text> [allowlist text] [today]
  printf '%s\n' "$3" > "$F"; printf '%s' "${4:-}" > "$T/allow.txt"
  o=$(scan "$T" "$T/allow.txt" "${5:-2026-01-01}")
  if [ "$2" = hit ]; then [ -n "$o" ] && grep -q '^VbmSimdProofs/Fix.lean:[0-9]' <<<"$o" || { echo "lint-proof-eval: self-test: not flagged (or no file:line): $1" >&2; exit 1; }
  else [ -z "$o" ] || { echo "lint-proof-eval: self-test: wrongly flagged: $1: $o" >&2; exit 1; }; fi
}
chk 'decide +kernel'   hit 'theorem t : 1 + 1 = 2 := by decide +kernel'
chk 'decide config'    hit 'theorem t : 1 + 1 = 2 := by decide (config := {kernel := true})'
chk 'native_decide'    hit 'theorem t : 1 + 1 = 2 := by native_decide'
chk 'decide := true'   hit 'theorem t : 1 + 1 = 2 := by simp (config := {decide := true})'
chk 'rfl big number'   hit "theorem t : (List.replicate $((NUM_MAX+1)) 0).length = $((NUM_MAX+1)) := by rfl"
chk 'decide big number' hit "theorem t : (List.range 100000).length = 100000 := by decide"
chk 'rfl big list'     hit "theorem t : [$(nums $((LIST_MAX+1)))].length = $((LIST_MAX+1)) := by rfl"
chk 'rfl deep nesting' hit "theorem t : $(printf '(%.0s' $(seq $((DEPTH_MAX+1)))) 1 $(printf ')%.0s' $(seq $((DEPTH_MAX+1)))) = 1 := by rfl"
chk 'Nat.rec simp big' hit "theorem t : f 100000 = 0 := by simp [Nat.rec]"
chk 'multi-line decl'  hit "theorem t :
    (List.replicate 100000 0).length = 100000 := by
  rfl"
chk 'just under: number' clean "theorem t : (List.replicate $NUM_MAX 0).length = $NUM_MAX := by rfl"
chk 'just under: list'   clean "theorem t : [$(nums $LIST_MAX)].length = $LIST_MAX := by rfl"
chk 'just under: depth'  clean "theorem t : $(printf '(%.0s' $(seq $DEPTH_MAX)) 1 $(printf ')%.0s' $(seq $DEPTH_MAX)) = 1 := by rfl"
chk 'big literal, no evaluation' clean "theorem t : (List.replicate 100000 0).length = 100000 := by simp"
chk 'comment only'       clean "-- by native_decide over 100000 elements would overflow
/- decide +kernel -/
theorem t : 1 + 1 = 2 := by rfl"
bigline="theorem t : (List.range 100000).length = 100000 := by decide"
A="VbmSimdProofs/Fix.lean	List.range 100000	2026-06-30	fixture reason
"
chk 'allowlisted, before expiry' clean "$bigline" "$A" 2026-06-30
chk 'allowlisted, after expiry'  hit   "$bigline" "$A" 2026-07-01
chk 'allowlist needle misses'    hit   "$bigline" "VbmSimdProofs/Fix.lean	nothing	2026-06-30	r
" 2026-01-01
chk 'allowlist other file'       hit   "$bigline" "VbmSimdProofs/Other.lean	List.range 100000	2026-06-30	r
" 2026-01-01
chk 'allowlist malformed (no reason)' hit "$bigline" "VbmSimdProofs/Fix.lean	List.range 100000	2026-06-30
" 2026-01-01
echo "lint-proof-eval: self-test ok"
out=$(scan . "$allow" "$(date +%F)")
[ -z "$out" ] || { echo "tier1: proof-by-evaluation over big data in VbmSimdProofs (restate via a shallow lemma; or allowlist with reason+expiry in $allow):" >&2; echo "$out" >&2; exit 1; }
echo "lint-proof-eval: ok"
