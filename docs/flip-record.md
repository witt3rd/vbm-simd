# Going public: the record

This repository started private and is made public by its owner. This page records what was checked, what the published history carries, and the order of the flip, so that a reader can see what "public-ready" meant here.

## History published as is

The history was **not** re-written or re-rooted. Every commit hash is one that consumers already pin (a Lake pin is a 40-hex commit, e.g. the one vbm-json's SIMD work uses), and a rewrite would break every pin and the lander's own checks. The exposure that is published:

- **The author identity.** The owner's name and e-mail appear as author and committer of 19 of the 20 commits (the same identity is already public in the owner's other repositories). The first commit is GitHub's web-flow `noreply` identity.
- **An old repository name.** Two commits (a README link, and the commit that renamed the link) carry the previous name of the VBM standard repository, which has since been renamed (GitHub redirects the old name). The public-readiness lint of the VBM standard lists that name as retired and refuses it in a tree; the current tree does not carry it.
- **Two public identifiers.** The release **public** signing key of the vendored lander (`scripts/land.signers`) and the update workflow's `noreply` bot address, both inside the vendored copy of vbm-land.
- **Task identifiers.** Three commits carry `Task`/`Task-ID` trailers naming work items of other public VBM repositories.
- Nothing else: no secret, no host name, no address, no local path, no other person's data, no word for the private build machines.

## What was checked (prep run of 2026-11-05; mirror of the remote taken at commit 040b4f1: `main`, 21 commits, no tags)

| Check | Result |
|---|---|
| gitleaks 8.30.1, full history of every ref of a fresh mirror of the remote, and the working tree | 0 findings |
| trufflehog 3.99.8, same scope | 0 verified, 0 unverified |
| the VBM public-readiness lint (hash list of private names, path patterns) over the tree | clean |
| a scan of every commit message, path, author line and changed line of all refs for the same hashes plus plain patterns (host names, home paths, e-mails, addresses) | only the accepted items above |
| `scripts/lint.sh` (this repository's own lint) and a grep of the tree for host names, addresses and home paths | clean (the one e-mail left is the vendored update bot's `noreply` address) |
| Tier 1 (`scripts/tier1.sh`) in a fresh `ubuntu:24.04` container after dependencies were fetched, with the network disconnected | passes, see "Clean-container proof" |
| a scratch Lake project that requires this repository by commit (the pin vbm-json's SIMD work uses, and main's tip) and builds and runs with the shim header | passes, see "Clean-container proof" |

## Clean-container proof

A fresh `ubuntu:24.04` (image digest `sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852`), no credentials. After the dependencies were fetched (git, python3 and PyYAML, build tools, mise and the pinned Lean 4.35.0) the network was disconnected, and in it, on commit 040b4f1: Tier 1 passes (41 s); the public-readiness lint passes; on the **flip-day tree** (the prepared patch applied) Tier 1 passes, the lint passes and Tier 2 passes (`leanchecker --fresh` of both libraries and nanoda: 59850 declarations, no typechecker errors); and a scratch Lake project that requires this repository by commit builds and runs a program through the trusted shim header, both at the commit vbm-json's SIMD work pins (`433268697353f3b5f0ad1197b2ab2475d270dae9`) and at the tip. The container has no systemd user manager, so the hosted-CI fallback of `scripts/run-scoped.sh` is the path exercised, as on a hosted runner.

## The flip, in order

Until the repository is public, CI runs on a self-hosted runner (the hosted runners are unavailable to a private repository), and `scripts/lint-workflows.py` allows that label only while `.github/visibility` says `private`. So the change that returns CI to hosted runners is prepared as a patch (`runs-on: ubuntu-latest`, the `jdx/mise-action` step that hosted runners need, `.github/visibility` set to `public`) and lands right after the visibility change:

1. The owner changes the visibility (`gh repo edit witt3rd/vbm-simd --visibility public --accept-visibility-change-consequences`) and checks that an anonymous `git clone https://github.com/witt3rd/vbm-simd` works.
2. At once, the settings below (the API refuses the fork-pull-request policy on a private repository, so it can only be set now). While the runner is still registered, CI has no `pull_request` trigger, so no outside code reaches it.
3. Apply the flip-day patch, then land it with `scripts/land-direct` (local Tier 1 runs the workflow lint on the patched tree), and read the push CI on a hosted runner: it must be green.
4. Deregister the runner (it is retired in the runner host's declared list; `gh api repos/witt3rd/vbm-simd/actions/runners` must then list none).
5. Tell the consumers (below); update the registry entry of the VBM standard when this repository is added.

## Settings at the flip (each has a read-back)

State read before the flip: the `protect-main` ruleset already exists and is active (rules `deletion` and `non_fast_forward`, no bypass actors); the workflow token is already `read` and cannot approve pull requests; no secret, deploy key or webhook exists; there are no tags and no releases.

1. Fork pull-request workflows need approval for **all outside collaborators**: `gh api -X PUT repos/witt3rd/vbm-simd/actions/permissions/fork-pr-contributor-approval -f approval_policy=all_external_contributors`; read back `gh api repos/witt3rd/vbm-simd/actions/permissions/fork-pr-contributor-approval`.
2. Read-only workflow token that cannot approve pull requests (already set; re-apply is harmless): `gh api -X PUT repos/witt3rd/vbm-simd/actions/permissions/workflow -f default_workflow_permissions=read -F can_approve_pull_request_reviews=false`; read back `gh api repos/witt3rd/vbm-simd/actions/permissions/workflow`.
3. Private vulnerability reporting: `gh api -X PUT repos/witt3rd/vbm-simd/private-vulnerability-reporting`; read back `gh api repos/witt3rd/vbm-simd/private-vulnerability-reporting` (`{"enabled":true}`).
4. Secret scanning and push protection: `gh api -X PATCH repos/witt3rd/vbm-simd -F 'security_and_analysis[secret_scanning][status]=enabled' -F 'security_and_analysis[secret_scanning_push_protection][status]=enabled'`; read back `gh api repos/witt3rd/vbm-simd --jq .security_and_analysis`.
5. Delete head branches on merge: `gh api -X PATCH repos/witt3rd/vbm-simd -F delete_branch_on_merge=true`; read back `gh api repos/witt3rd/vbm-simd --jq .delete_branch_on_merge`.
6. Protect `main` from deletion and non-fast-forward updates (no required pull request, no bypass list, so landing still works): the ruleset `protect-main` is already in place; read back `gh api repos/witt3rd/vbm-simd/rules/branches/main --jq '[.[].type]'` (`["deletion","non_fast_forward"]`), then one real landing (the flip-day patch is one). Only if it were missing: `gh api repos/witt3rd/vbm-simd/rulesets --input scripts/land/templates/ruleset-protect-main.json`.
7. Release tags (`v*`): none exist. When the first release is cut, before the tag is pushed: `gh api repos/witt3rd/vbm-simd/rulesets --input scripts/land/templates/ruleset-protect-release-tags.json`; read back `gh api repos/witt3rd/vbm-simd/rulesets --jq '.[].name'` lists `protect-release-tags`.
8. No workflow uses `pull_request_target` (checked by `scripts/lint-workflows.py`), every workflow declares read-only `permissions:`, no deploy key or stale secret exists (read back `gh api repos/witt3rd/vbm-simd/keys` and `gh api repos/witt3rd/vbm-simd/actions/secrets`: both empty).

## Consumers

vbm-json's SIMD work (a branch, not yet on its `main`) requires this repository by commit (`https://github.com/witt3rd/vbm-simd` at `433268697353f3b5f0ad1197b2ab2475d270dae9`, the commit that made the shim header path absolute so that a consuming Lake project builds). That commit is in the published history and is unchanged; nothing is re-pinned. While this repository is private a hosted runner cannot fetch the dependency, so vbm-json's hosted CI can only build it once the flip is done. The clean-container proof builds a scratch project that requires this repository at that exact commit.
