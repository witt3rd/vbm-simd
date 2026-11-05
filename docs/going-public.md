# Before going public

Do these in order; each is a checkable fact.

1. `runs-on` is a GitHub-hosted label in every workflow (no `self-hosted`), and the repository's self-hosted runner is removed
   (`gh api repos/OWNER/REPO/actions/runners` lists none).
2. `.github/visibility` says `public` (`scripts/lint-workflows.py` fails Tier 1 when a workflow names `self-hosted` and it does not say `private`).
3. `LAND_RED_MODE` in `scripts/land.conf` is unchanged (`push`).
4. The settings checklist `scripts/land/templates/PUBLIC-REPO-SETTINGS.md` is done.
