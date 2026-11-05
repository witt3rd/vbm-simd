#!/usr/bin/env bash
# Gate-edit approvals (docs/gate-edit-approvals.md). Sourced by bin/land-direct, never run.
#
# A removed or changed line in a gate-defining file is accepted ONLY on an exact diff-hash match against an approval already on the base branch.
# The approvals file (LAND_APPROVALS, default scripts/gate-edit-approvals.txt) holds one record per line:
#
#     FILE | sha256 of the exact diff of that file | reason | YYYY-MM-DD
#
# The hash is the sha256 of the CANONICAL DIFF of FILE: what `land-direct --print-gate-diff-hash FILE` prints (ga_canon below: fixed flags, no config, `index` lines dropped).
# The rules (each one has a negative self-test in tests/test_approvals.sh):
#   - approvals are read from the BASE branch, never from the change: a landing cannot approve itself;
#   - an approval lands ALONE: a commit that adds a record changes no other file, adds exactly ONE line and removes none, and so does the landing that holds it (the edit comes in a later landing);
#   - one-time: a landing whose diff of FILE hashes to a record on base must REMOVE that record in the same landing (the consumption); a record is never reusable;
#   - a record removed without being consumed is refused (flagged), unless it is stale (the window closed: tidying up) or withdrawn by an `Approval-Withdrawn: FILE <hash prefix>` trailer in a landing that changes nothing else (announced to the judge);
#   - stale (older than LAND_APPROVAL_DAYS) or future-dated records approve nothing; a malformed or self-referencing record added is refused.
# HONEST LIMIT: an agent with landing rights could write its own approval line. The control is that approvals are visible one-commit records the independent judge
# reads before the edit lands: the approval commit is announced to the judge BEFORE the edit commit, always.

# ga_canon DIR BASE HEAD FILE: the canonical diff of FILE between two trees (stdout). Same flags and no repository or user configuration that changes diff output.
ga_canon() {
  git -C "$1" -c core.quotepath=off -c diff.noprefix=false -c diff.mnemonicPrefix=false -c diff.renames=false -c diff.algorithm=myers -c diff.indentHeuristic=true -c diff.context=0 \
    -c diff.interHunkContext=0 -c core.abbrev=40 -c color.diff=false \
    diff --no-ext-diff --no-textconv --no-color --no-renames --text -U0 --inter-hunk-context=0 --src-prefix=a/ --dst-prefix=b/ "$2" "$3" -- "$4" \
    | sed -E '/^index [0-9a-f]+\.\.[0-9a-f]+( [0-7]+)?$/d'
}
# ga_hash DIR BASE HEAD FILE: the sha256 of the canonical diff; prints nothing and returns 1 when FILE does not differ.
ga_hash() { local c; c=$(ga_canon "$@"; echo x) || return 1; c=${c%x}; [ -n "$c" ] || return 1; printf '%s' "$c" | sha256sum | cut -d' ' -f1; }

ga_rec_re='^([A-Za-z0-9_@+-][A-Za-z0-9_./@+-]*) \| ([0-9a-f]{64}) \| ([^|]|[^|][^|]*[^|]) \| ([0-9]{4}-[0-9]{2}-[0-9]{2})$'
# ga_valid_path P: a plain repository path: no leading dot-slash or slash, no empty or dot components.
ga_valid_path() { [[ "$1" =~ ^[A-Za-z0-9_@+-][A-Za-z0-9_./@+-]*$ ]] && [[ "/$1/" != *"/./"* ]] && [[ "/$1/" != *"/../"* ]] && [[ "$1" != */ ]] && [[ "$1" != *//* ]]; }
# ga_age_days DATE: whole days between that UTC date and today; returns 1 for a date that does not exist.
ga_age_days() { local t; t=$(date -u -d "$1 00:00:00" +%s 2>/dev/null) || return 1; echo $(( ( $(date -u +%s) - t ) / 86400 )); }
# ga_fresh DATE DAYS: 0 when the record is inside the window: not older than DAYS days, not dated later than tomorrow (an author's clock may lead by a day).
ga_fresh() { local a; a=$(ga_age_days "$1") || return 1; [ "$a" -ge -1 ] && [ "$a" -le "$2" ]; }
# ga_records: read an approvals file on stdin; print each valid record as one line `FILE|HASH|DATE|<the record as written>`; every other non-blank, non-comment line is printed to fd 3 (stderr when not open).
ga_records() {
  local line f h d
  while IFS= read -r line || [ -n "$line" ]; do
    line=${line%$'\r'}
    [[ "$line" =~ ^[[:space:]]*(#.*)?$ ]] && continue
    if [[ "$line" =~ $ga_rec_re ]]; then f=${BASH_REMATCH[1]}; h=${BASH_REMATCH[2]}; d=${BASH_REMATCH[4]}   # (ga_valid_path runs its own match: take these first)
      if ga_valid_path "$f" && date -u -d "$d" +%s >/dev/null 2>&1; then printf '%s|%s|%s|%s\n' "$f" "$h" "$d" "$line"; continue; fi
    fi
    printf '%s\n' "$line" >&3
  done
}

# ga_early DIR COMMITS APPROVALS_PATH: the per-commit rule, before any rebase: a commit that adds an approval record changes no other file. Prints the refusal and returns 1.
ga_early() {
  local d=$1 commits=$2 p=$3 c others added ns
  for c in $commits; do
    added=$(git -C "$d" diff -U0 --no-renames "$c^" "$c" -- "$p" 2>/dev/null | sed -n 's/^+\([^+].*\)$/\1/p' | grep -vE '^[[:space:]]*(#.*)?$' || true)
    [ -n "$added" ] || continue
    others=$(git -C "$d" diff-tree --no-commit-id --name-only -r --no-renames "$c" | grep -vxF -- "$p" || true)
    echo "land-direct: APPROVAL COMMIT: announce to the judge before landing the edit, with the diff hash and the FULL edit diff (${c:0:12} adds a gate-edit approval to $p)"
    if [ -n "$others" ]; then
      echo "land-direct: commit ${c:0:12} adds a gate-edit approval to $p and changes other files ($(echo $others)): an approval lands ALONE, in its own commit and its own landing, and is announced to the judge BEFORE the edit it approves (docs/gate-edit-approvals.md)." >&2
      return 1
    fi
    ns=$(git -C "$d" diff --numstat --no-renames "$c^" "$c" -- "$p" | cut -f1,2)
    if [ "$ns" != "1"$'\t'"0" ]; then
      echo "land-direct: commit ${c:0:12} changes $p by $(tr '\t' '/' <<<"$ns") lines added/removed: an approval commit adds exactly ONE line (one record) and removes none, and changes no other file." >&2
      return 1
    fi
  done
  return 0
}

# ga_withdrawn FILE HASH TRAILERS: 0 when a trailer line `FILE PREFIX` names this record (PREFIX: 12 or more leading hex digits of the hash).
ga_withdrawn() { local tf th; while read -r tf th; do [ "$tf" = "$1" ] && [[ "$2" == "$th"* ]] && return 0; done <<<"$3"; return 1; }

# ga_judge WT BASEREF APPROVALS_PATH DAYS APPEND_ONLY_GLOBS STATE_DIR: the generic judge on the rebased tree WT against BASEREF. Prints the verdict; returns 0 (nothing refused) or 1 (refused: the reasons are on stderr).
# Writes $STATE_DIR/approved-gate-edits.txt: `FILE HASH` of every approval this landing consumes (the hooks read it as $LAND_GATE_APPROVED_FILE).
ga_judge() {
  local wt=$1 base=$2 ap=$3 days=$4 globs=$5 state=$6 rec f h d line changed others g e ns del mode
  local B=$state/ga-base.rec H=$state/ga-head.rec ADD=$state/ga-added.rec REM=$state/ga-removed.rec USED=$state/ga-used.rec JB=$state/ga-base.junk JH=$state/ga-head.junk
  local -A fhash=()
  ga_refused=0; ga_refuse() { echo "land-direct: $*" >&2; ga_refused=1; }
  : > "$state/approved-gate-edits.txt"; : > "$USED"
  if git -C "$wt" cat-file -e "HEAD:$ap" 2>/dev/null && [ "$(git -C "$wt" ls-tree HEAD -- "$ap" | cut -d' ' -f1)" != 100644 ]; then ga_refuse "$ap is not a regular, non-executable file: not landing."; fi
  { git -C "$wt" show "$base:$ap" 2>/dev/null || true; } | ga_records >"$B" 3>"$JB"
  { git -C "$wt" show "HEAD:$ap" 2>/dev/null || true; } | ga_records >"$H" 3>"$JH"
  changed=$(git -C "$wt" -c core.quotepath=off diff --name-only --no-renames "$base" HEAD)
  grep -vxFf "$B" "$H" > "$ADD" || true; grep -vxFf "$H" "$B" > "$REM" || true
  # a line the change adds that is not an approval record: refused (a malformed record must not pass for an approval)
  while IFS= read -r line; do [ -n "$line" ] || continue
    ga_refuse "$ap: a line that is not an approval record ('FILE | sha256 | reason | YYYY-MM-DD'; the file may not be one of these either): $line"
  done < <(grep -vxFf "$JB" "$JH" || true)
  # R1: added records: alone, in the window, not about the approvals file
  if [ -s "$ADD" ]; then
    echo "land-direct: $(wc -l < "$ADD") approval record(s) added to $ap; the edit each approves lands later, in its own landing, and removes the record"
    ns=$(git -C "$wt" diff --numstat --no-renames "$base" HEAD -- "$ap" | cut -f1,2)
    [ "$ns" = "1"$'\t'"0" ] || ga_refuse "this landing adds an approval to $ap but changes it by $(tr '\t' '/' <<<"$ns") lines added/removed: an approval landing adds exactly ONE line (one record), removes none, and carries one approval only."
    others=$(grep -vxF -- "$ap" <<<"$changed" || true)
    [ -z "$others" ] || ga_refuse "this landing adds a gate-edit approval to $ap and changes other files ($(echo $others)): an approval lands ALONE (the same landing as an edit it approves is a self-approval); the edit comes after the judge has read the approval."
    while IFS='|' read -r f h d line; do
      [ "$f" != "$ap" ] || ga_refuse "an approval may not name the approvals file itself: $line"
      ga_fresh "$d" "$days" || ga_refuse "an approval dated $d is outside the window (at most $days days old, not future-dated): $line"
    done < "$ADD"
  fi
  # R3: what the landing's net diff consumes: the base's records whose hash is the net diff of their file
  while IFS='|' read -r f h d line; do
    [ -n "$f" ] || continue
    grep -qxF -- "$f" <<<"$changed" || continue
    [ -n "${fhash[$f]+x}" ] || fhash[$f]=$(ga_hash "$wt" "$base" HEAD "$f" || true)
    [ "${fhash[$f]}" = "$h" ] || continue
    if ga_fresh "$d" "$days"; then
      printf '%s|%s|%s|%s\n' "$f" "$h" "$d" "$line" >> "$USED"; printf '%s %s\n' "$f" "$h" >> "$state/approved-gate-edits.txt"
      grep -qxF -- "$f|$h|$d|$line" "$REM" || ga_refuse "the approval for $f (${h:0:12}) is consumed by this landing and its line is still in $ap: one-time approvals are removed in the landing that uses them (delete the line in this landing)."
    else ga_refuse "the approval for $f (${h:0:12}, dated $d) is stale (older than $days days): it approves nothing; a new approval commit comes first."
    fi
  done < "$B"
  # R2: a record removed without being consumed is flagged (a stale one may be tidied away; a trailer `Approval-Withdrawn: FILE <first 12+ hex of the hash>` in this landing's commits withdraws a fresh one)
  local wd; wd=$(git -C "$wt" log --format=%B "$base..HEAD" | tr -d '\r' | sed -nE 's/^Approval-Withdrawn: +([^ ]+) +([0-9a-f]{12,64}) *$/\1 \2/p')
  while IFS='|' read -r f h d line; do
    [ -n "$f" ] || continue
    grep -qxF -- "$f|$h|$d|$line" "$USED" && continue
    ga_fresh "$d" "$days" || continue
    if ga_withdrawn "$f" "$h" "$wd"; then   # withdrawn by a trailer: announced, and the landing carries nothing else
      others=$(grep -vxF -- "$ap" <<<"$changed" || true)
      [ -z "$others" ] || ga_refuse "the approval for $f (${h:0:12}) is withdrawn by trailer in a landing that also changes other files ($(echo $others)): a withdrawal lands ALONE."
      echo "land-direct: APPROVAL WITHDRAWN: announce to the judge: $f (${h:0:12}) is withdrawn by trailer without being used"; continue
    fi
    ga_refuse "the approval for $f (${h:0:12}) was removed without being consumed (its diff is not what this landing changes): an approval line is removed only by the landing that uses it, or once it is stale. FLAGGED."
  done < "$REM"
  # append-only files: a removed or changed line (or a deleted file, a mode change) needs an approval that this landing consumes
  local -a gl=(); read -ra gl <<<"$globs"
  if [ ${#gl[@]} -gt 0 ]; then
    while IFS= read -r f; do [ -n "$f" ] || continue
      e=0; for g in "${gl[@]}"; do [[ "$f" == $g ]] && e=1; done; [ "$e" = 1 ] || continue
      git -C "$wt" cat-file -e "$base:$f" 2>/dev/null || continue                                  # a new file only gains
      ns=$(git -C "$wt" diff --numstat --no-renames "$base" HEAD -- "$f" | cut -f2); del=${ns:-0}; mode=
      git -C "$wt" cat-file -e "HEAD:$f" 2>/dev/null || del=gone
      [ "$(git -C "$wt" ls-tree "$base" -- "$f" | cut -d' ' -f1)" = "$(git -C "$wt" ls-tree HEAD -- "$f" 2>/dev/null | cut -d' ' -f1)" ] || mode=mode
      [ "$del" != 0 ] || [ -n "$mode" ] || continue
      h=$(ga_hash "$wt" "$base" HEAD "$f" || true)
      if [ -n "$h" ] && grep -qxF -- "$f $h" "$state/approved-gate-edits.txt"; then echo "land-direct: gate edit APPROVED: $f (${h:0:12}) removes or changes lines; the approval is consumed by this landing"
      else
        ga_refuse "$f is a gate-defining file that may only GAIN lines (LAND_GATE_APPEND_ONLY) and this landing removes or changes some ($del removed${mode:+, mode changed}): refused unless an approval for exactly this diff is already on the base branch. The approval is a record in $ap, landed ALONE and announced to the judge BEFORE the edit; hash: $h (land-direct --print-gate-diff-hash $f)."
        git -C "$wt" diff -U0 --no-renames "$base" HEAD -- "$f" | grep -E '^-[^-]' | sed -n '1,6s/^/land-direct:   /p' >&2 || true
      fi
    done <<<"$changed"
  fi
  [ "$ga_refused" = 0 ]
}
# ga_judge_run ARGS...: ga_judge in a bash of its own with `set -e`, which a function called from `||` never has: any command that fails unexpectedly stops the judge, and the landing is refused (fail closed).
ga_judge_run() {
  bash -c 'set -eEuo pipefail; trap '"'"'echo "land-direct: the gate-edit judge failed unexpectedly (line $LINENO): refusing" >&2'"'"' ERR; . "$1"; shift; ga_judge "$@"' _ "${BASH_SOURCE[0]}" "$@"
}
