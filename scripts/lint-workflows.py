#!/usr/bin/env python3
"""Structural validity of .github/workflows/*.yml (Tier 1): the file parses, has a trigger and at least one job, every job has steps (or `uses`),
and every step has exactly one of `uses` / `run`, and the public-repository rules: no `self-hosted` runner anywhere (`runs-on` is a GitHub-hosted label), no `pull_request_target` trigger, no `secrets.` other than the default GITHUB_TOKEN, and `with:` only on a `uses` step (a step inserted between a `uses` and its `with` broke a workflow once:
zero jobs ran). Uses actionlint too when it is on PATH. Usage: lint-workflows.py [file|dir ...]  (default .github/workflows)"""
import glob, json, os, re, shutil, subprocess, sys
try:
    import yaml
except ImportError:
    print("lint-workflows: PyYAML is missing (apt install python3-yaml)", file=sys.stderr); sys.exit(2)

def check(path):
    errs = []
    try:
        d = yaml.safe_load(open(path))
    except Exception as e:
        return [f"{path}: does not parse: {e}"]
    if not isinstance(d, dict):
        return [f"{path}: not a mapping"]
    if True not in d and "on" not in d:  # PyYAML reads the key `on` as True
        errs.append(f"{path}: no `on:` trigger")
    on = d.get(True, d.get("on"))
    trig = on if isinstance(on, (str, list, dict)) else []
    if "pull_request_target" in trig:
        errs.append(f"{path}: the pull_request_target trigger is forbidden (it runs fork-controlled code with repository privileges)")
    for m in re.finditer(r"secrets\.([A-Za-z0-9_]+)", open(path).read()):
        if m.group(1) != "GITHUB_TOKEN":
            errs.append(f"{path}: secret {m.group(1)} is used: no secret may be used (fork pull requests, a public repository)")
    jobs = d.get("jobs")
    if not isinstance(jobs, dict) or not jobs:
        errs.append(f"{path}: no jobs (zero jobs would run)")
        return errs
    for jn, j in jobs.items():
        if not isinstance(j, dict):
            errs.append(f"{path}: job {jn} is not a mapping"); continue
        if "uses" in j:
            continue
        if "runs-on" not in j:
            errs.append(f"{path}: job {jn} has no runs-on")
        elif "self-hosted" in json.dumps(j["runs-on"]):
            errs.append(f"{path}: job {jn} runs on a self-hosted runner: public-repository workflows use GitHub-hosted runners only")
        elif not re.fullmatch(r"(ubuntu|windows|macos)-[a-z0-9.-]+", str(j["runs-on"])):
            errs.append(f"{path}: job {jn} runs-on {j['runs-on']!r} is not a plain GitHub-hosted label (no expressions, no groups)")
        steps = j.get("steps")
        if not isinstance(steps, list) or not steps:
            errs.append(f"{path}: job {jn} has no steps"); continue
        for i, s in enumerate(steps):
            if not isinstance(s, dict):
                errs.append(f"{path}: job {jn} step {i} is not a mapping"); continue
            nm = s.get("name") or s.get("uses") or s.get("run") or "?"
            if ("uses" in s) == ("run" in s):
                errs.append(f"{path}: job {jn} step {i} ({str(nm)[:40]}) must have exactly one of uses/run")
            if "with" in s and "uses" not in s:
                errs.append(f"{path}: job {jn} step {i} ({str(nm)[:40]}) has `with:` but no `uses:`")
    return errs

def main(args):
    files = []
    for a in args or [".github/workflows"]:
        files += sorted(glob.glob(os.path.join(a, "*.y*ml"))) if os.path.isdir(a) else [a]
    if not files:
        print("lint-workflows: no workflow files found", file=sys.stderr); return 1
    errs = [e for f in files for e in check(f)]
    if not errs and shutil.which("actionlint") and subprocess.run(["actionlint", "-version"], capture_output=True).returncode == 0:
        r = subprocess.run(["actionlint", *files], capture_output=True, text=True)
        if r.returncode: errs.append("actionlint:\n" + r.stdout + r.stderr)
    for e in errs: print("lint-workflows:", e, file=sys.stderr)
    if not errs: print(f"lint-workflows: {len(files)} workflow file(s) ok")
    return 1 if errs else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
