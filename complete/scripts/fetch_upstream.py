#!/usr/bin/env python3
"""Retrieve the immutable import closure and verify every source hash."""
import concurrent.futures, hashlib, json, pathlib, urllib.request
root = pathlib.Path(__file__).resolve().parents[1]
lock = json.loads((root / "upstream-lock.json").read_text())
def fetch(item):
    module, record = item
    target = root / record["path"]
    if not target.exists() or hashlib.sha256(target.read_bytes()).hexdigest() != record["sha256"]:
        url = "https://raw.githubusercontent.com/plby/lean-proofs/" + lock["commit"] + "/" + lock["source_prefix"] + record["path"]
        with urllib.request.urlopen(url, timeout=60) as response:
            content = response.read()
        if hashlib.sha256(content).hexdigest() != record["sha256"]:
            raise RuntimeError("Source hash mismatch: " + module)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    return module
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
    verified = list(pool.map(fetch, lock["modules"].items()))
print(f"Verified {len(verified)} hash-pinned upstream modules.")
