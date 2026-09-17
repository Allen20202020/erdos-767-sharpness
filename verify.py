#!/usr/bin/env python3
"""Build, audit axiom closures, and replay the actual compiled proof."""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent
OUT = ROOT / "verification"
OUT.mkdir(exist_ok=True)
checks = []


def run(name, args):
    p = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT)
    # Retain full results without publishing local home directory names.
    output = re.sub(r"/Users/[^\s:]+", "<local-path>", p.stdout)
    (OUT / (name + ".log")).write_text(output)
    checks.append({"name": name, "command": args, "exit_code": p.returncode})
    if p.returncode:
        raise SystemExit(f"{name} failed; inspect verification/{name}.log")
    return p.stdout


run("lean-version", ["lake", "env", "lean", "--version"])
run("build", ["lake", "build"])
audit = run("axioms", ["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"])
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit)
expected = {"JSP628." + n for n in (
    "join_matching_avoids", "construction_avoids", "construction_edges",
    "construction_spec", "critical_arithmetic", "threshold_sharpness")}
assert {name for name, _ in reports} == expected, "Missing or unexpected axiom report"
allow = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in reports:
    assert {x.strip() for x in axioms.split(",") if x.strip()} <= allow, (name, axioms)
run("kernel-replay", ["lake", "env", "leanchecker", "--fresh", "--verbose",
                      "JSP628.Sharpness"])
files = ["JSP628.lean", "JSP628/Sharpness.lean", "Audit.lean", "lean-toolchain",
         "lakefile.toml", "lake-manifest.json", "verify.py"]
manifest = {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest() for f in files}
result = {
    "verified_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "checks": checks, "axiom_reports": dict(reports), "source_sha256": manifest,
    "limitations": ["Contributor-run checks; not organizer verification",
                    "leanchecker uses the official Lean kernel implementation",
                    "Imported dependencies use compiled Mathlib caches; no full source rebuild",
                    "This is the sharpness component, not the full extremal formula"],
}
(OUT / "summary.json").write_text(json.dumps(result, indent=2) + "\n")
print("Build, six axiom audits, and fresh kernel replay passed.")
