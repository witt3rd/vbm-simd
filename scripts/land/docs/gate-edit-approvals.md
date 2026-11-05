# Gate-edit approvals

A gate-defining file that may only GAIN lines (a ratchet, a Tier 1 script, an attack list) sometimes needs a line removed or changed for a good reason. The lander never lets a
change decide that for itself. A removed or changed line is accepted **only** on an exact diff-hash match against an **approval that is already on the base branch**.

## The file

`scripts/gate-edit-approvals.txt` (key `LAND_APPROVALS`; it cannot be empty, and the file is always in the protected set). One record per line, `#` comments and blank lines allowed:

    FILE | sha256 of the exact diff of that file | reason | YYYY-MM-DD

`FILE` is a plain repository path, the hash is lower-case hex, the reason is free text without `|`, the date is UTC. Anything else on a line is not an approval, and a line like that
may not be added.

## The hash: the canonical diff

    land-direct --print-gate-diff-hash FILE [<rev>]     # the sha256 on stdout; the record to write on stderr
    land-direct --print-gate-diff FILE [<rev>]          # the canonical diff itself

The canonical diff of FILE is what `git diff --no-ext-diff --no-textconv --no-color --no-renames --text -U0 --diff-algorithm=myers` (fixed prefixes `a/` `b/`, no user or repository diff
configuration, the `index` line dropped) prints for FILE between the **merge base with `origin/<base>`** and `<rev>` (default `HEAD`): the NET diff of the whole landing, not of one commit. The
hash binds the path, the hunks, the mode lines and the removed and added text; it is what the lander computes on the rebased tree, so the author and the judge agree.

## The rules (each has a negative self-test in `tests/test_approvals.sh`, each guard a mutant in `tests/test_mutations.sh`)

1. **Read from the base branch.** The lander reads approvals from `origin/<base>`, never from the change: a landing cannot approve itself. `LAND_GATE_APPEND_ONLY` (shell patterns) names the files that may only gain lines; a
   landing whose net diff removes or changes a line of one (or deletes it, or changes its mode) is refused (exit 12) unless an approval for exactly that diff is on base.
2. **An approval lands alone, first, and it is ONE line.** A commit that adds a record changes no other file, adds exactly ONE line (one record) and removes none; the landing that carries it is the same (one approval per landing, no tidying alongside). It passes Tier 1 like any change. The edit lands in a LATER landing. The approval commit is announced to the
   judge before the edit commit, always, with the diff hash AND the FULL edit diff (`land-direct --print-gate-diff FILE`): the hash binds the exact diff the judge read: `land-direct` prints `APPROVAL COMMIT: announce to the judge before landing the edit`.
3. **One-time.** A landing whose diff of FILE hashes to a record on base must REMOVE that record in the same landing (the consumption), or it is refused. Nothing else keeps a log: the record's disappearance in the landing
   is the log. Removing a record is how it is used up; a record can never approve a second edit. (Adding a record next to the edit is not allowed, see 2; removing one is the consumption.)
4. **A stale approval approves nothing.** A record older than `LAND_APPROVAL_DAYS` (default 7) days, or dated more than a day ahead, is refused when used, and refused when added.
5. **A record removed without being consumed is flagged and refused.** (A stale one may be tidied away: it approves nothing.) A fresh one is **withdrawn** by a trailer `Approval-Withdrawn: FILE <first 12 or more hex digits of its hash>` on a commit of the landing, and that landing changes nothing but the approvals file; `land-direct` prints `APPROVAL WITHDRAWN: announce to the judge`: the withdrawal is as visible as the approval was. Re-dating or editing a record is a removal of the old one. Deleting the file is the same.
6. **Malformed or self-referencing records are refused.** A record that does not parse (or names the approvals file) may not be added.
7. **The judge fails closed.** It runs in a shell of its own with `set -e`: an unexpected failure refuses the landing.

A repository's own `post-rebase` judge (a stricter one) may ask for the approvals this landing consumes: `$LAND_GATE_APPROVED_FILE` lists `FILE HASH` per consumed approval; the lander has already enforced 1 to 7.

## How to edit a gate line (the author's steps)

1. Make the edit in your worktree; commit it. Run `land-direct --print-gate-diff-hash FILE` and note the hash. (Do not land yet.)
2. In a fresh worktree off `origin/<base>`: add the record to `scripts/gate-edit-approvals.txt`, one commit that changes nothing else, `scripts/land-direct`. **Tell the judge before the next step**: the approval is the visible record he reads.
3. When the judge has read it: in the edit's worktree, remove the record (a commit, or in the edit's commit), rebase, `scripts/land-direct`. The same landing carries the edit and the consumption.
4. If the edit is not landed within `LAND_APPROVAL_DAYS`, the approval is stale: a new approval comes first.

## The honest limit

**An agent with landing rights could write its own approval line.** The control is that approvals are visible one-commit records the independent judge reads before the edit lands, so the approval commit is announced to the judge
BEFORE the edit commit, always. The lander makes the sequence mechanical (rules 1 to 7: no self-approval in the same landing, no reuse, no stale or quiet approval, nothing but the exact diff), not independent: it
cannot tell an approval the judge read from one he did not. The record's own reason line is the place to say why; the announcement is the control.
