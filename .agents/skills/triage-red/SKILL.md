---
name: triage-red
description: >-
  Main is red or land-direct exited 10: read the failing Tier 1 step, decide infrastructure skip versus real red, and fix forward or revert. Use when land-direct says main is red, or a push CI run of main failed.
---

# triage-red

Red = the `tier1` job of the latest push run of `ci.yml` on main failed (and the failure is not infrastructure). While red or frozen only a **fix or a revert** lands: a change touching only `LAND_FIX_PATHS` (tests, CI) and nothing in `LAND_PROTECTED`.

## Steps

1. Confirm what the lander sees: `scripts/land/bin/land-red; echo $?` (0 ok, 10 red, 14 frozen, 20 not knowable).
2. Find the run and the failing step:
   ```
   gh run list --workflow ci.yml --branch main --limit 5
   gh run view <id> --json jobs --jq '.jobs[]|[.name,.conclusion]|@tsv'
   gh run view <id> --log-failed | tail -60
   ```
3. Classify:
   - **Infrastructure** (runner never started, network error, billing/quota, cancelled): not red. Re-run it: `gh run rerun <id> --failed`. If the lander still blocks, re-run once, then stop and report; do not touch the classifier.
   - **Real red**: the commit's own content failed. Continue.
   - Exit 20 (not knowable): `gh auth status`, network; fix access, do not bypass.
4. Reproduce locally in a **new worktree** off fresh `origin/main`, running the Tier 1 command from `scripts/land.conf`.
5. Choose, fastest first: **revert** (`git revert <sha>`) if the cause is clear and small, otherwise **fix forward** if the fix is one small change.
6. Land it as the fix. It is recognised by its subject and paths: `fix(ci): ...` or `fix(tests): ...` touching only `LAND_FIX_PATHS` (when set) and nothing protected, or a git `Revert "..."` commit (a true revert may touch anything it undoes). Then `scripts/land-direct`; if the lander does not recognise it but it truly is the fix, `LAND_FIX_FOR_RED=1 scripts/land-direct`. Exit 12 means it touches the protected set: that needs a person.
7. Wait for the push CI of the fix; main is green again when `tier1` passes.

## Verify

`scripts/land/bin/land-red` exits 0, and `gh run list --workflow ci.yml --branch main --limit 1` shows success.

## Do NOT

- Do not push to main directly, or edit on main ("hotfix").
- Do not remove a freeze you did not set (see `hold-and-freeze`).
- Do not widen `infra-re.sh` or `LAND_RED_MODE=off` to get past red.
- Do not re-run CI repeatedly to make a real red go away.
