#!/usr/bin/env python3
"""Verify pinned sources, complete proof, all selected theorems and bundled project-kernel replay."""
import datetime, hashlib, json, pathlib, re, subprocess
root = pathlib.Path(__file__).resolve().parent
out = root / "evidence"
out.mkdir(exist_ok=True)
checks = []
def run(name, args):
    p = subprocess.run(args, cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (out / (name + ".log")).write_text(re.sub(r"/Users/[^\s:]+", "<local-path>", p.stdout))
    checks.append({"name": name, "command": args, "exit_code": p.returncode})
    if p.returncode:
        raise SystemExit(name + " failed")
    return p.stdout
run("upstream", ["python3", "scripts/fetch_upstream.py"])
for path in list((root / "ErdosProblems").rglob("*.lean")) + list((root / "JSP628Full").rglob("*.lean")):
    source = path.read_text()
    assert not re.search(r"\b(sorry|admit|native_decide)\b", source), path
run("lean-version", ["lake", "env", "lean", "--version"])
run("build", ["lake", "build"])
audit = run("axioms", ["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"])
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit)
expected = set(['JSP628.join_matching_avoids', 'JSP628.construction_avoids', 'JSP628.construction_edges', 'JSP628.construction_spec', 'JSP628.critical_arithmetic', 'JSP628.threshold_sharpness', 'JSP628Full.original_resolution', 'JSP628Full.predicate_iff', 'JSP628Full.critical_extremal_strict', 'JSP628Full.stabilizingThreshold_spec', 'JSP628Full.every_threshold_lower', 'JSP628Full.stabilization_bounds'])
assert {n for n, _ in reports} == expected
for n, axioms in reports:
    assert {a.strip() for a in axioms.split(",") if a.strip()} <= {"propext", "Classical.choice", "Quot.sound"}, n
run("kernel-replay", ["lake", "env", "leanchecker", "--verbose", "JSP628Full"])
files = ['JSP628Full.lean', 'JSP628Full/Main.lean', 'JSP628Full/Sharpness.lean', 'Audit.lean', 'upstream-lock.json', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'verify.py', 'scripts/fetch_upstream.py']
result = {"verified_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "checks": checks, "axiom_reports": dict(reports), "source_sha256": {f: hashlib.sha256((root/f).read_bytes()).hexdigest() for f in files}, "limitations": ["Contributor-run checks, not organizer or independent human verification", "leanchecker uses the official Lean kernel", "Cached imported dependencies; no full Mathlib source rebuild", "The forcing proof is credited prior work; the sharpness and least stabilization threshold bounds are the new contribution"]}
(out / "summary.json").write_text(json.dumps(result, indent=2) + "\n")
print("Pinned source, complete build, twelve theorem audits and project replay passed.")
