#!/usr/bin/env python3
"""Reproduce the unchanged generic reduction extraction with pinned tools."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument("--charon", type=Path, required=True)
parser.add_argument("--aeneas", type=Path, required=True)
args = parser.parse_args()
scope = json.loads((ROOT / "scope.json").read_text())
source = (ROOT / scope["source_repository"]).resolve()
inventory = json.loads((ROOT / "audit/source-inventory.json").read_text())
for item in inventory["files"]:
    if hashlib.sha256((source / item["path"]).read_bytes()).hexdigest() != item["sha256"]:
        raise SystemExit("source drift: " + item["path"])
for path, expected in scope["source_build_inputs_sha256"].items():
    if hashlib.sha256((source / path).read_bytes()).hexdigest() != expected:
        raise SystemExit("build input drift: " + path)
out = ROOT / "extraction/reduce"
out.mkdir(parents=True, exist_ok=True)
env = dict(os.environ, RUSTUP_TOOLCHAIN="nightly-2026-09-17",
           CARGO_TARGET_DIR=str(ROOT / "tooling/reduce-charon-target"), CARGO_BUILD_JOBS="2")
commands = [
    [str(args.charon.resolve()), "cargo", "--preset=aeneas", "--sysroot=default",
     "--dest-file=" + str(out / "reduce.llbc"),
     "--start-from=bulksketch::field::gf64::reduce", "--", "--manifest-path",
     str(source / "Cargo.toml"), "-p", "bulksketch", "--lib", "--locked"],
    [str(args.aeneas.resolve()), "-backend", "lean", "-split-files", "-dest",
     str(out / "Reduce"), str(out / "reduce.llbc")],
]
(out / "Reduce").mkdir(exist_ok=True)
records = []
for label, command in zip(["charon", "aeneas"], commands):
    with (out / (label + ".log")).open("w") as log:
        result = subprocess.run(command, cwd=source, env=env, stdout=log,
                                stderr=subprocess.STDOUT, timeout=300)
    records.append({"tool": label, "command": command, "exit_code": result.returncode})
    if result.returncode:
        raise SystemExit(label + " failed; see extraction/reduce/" + label + ".log")
    if label == "charon" and json.loads((out / "reduce.llbc").read_text())["has_errors"]:
        raise SystemExit("incomplete LLBC")
receipt = {"source_commit": scope["source_commit"],
           "checkout_commit": subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip(),
           "charon_commit": "7b462d9159db2ed3015162352183906a30bfafc6",
           "aeneas_commit": "ab34bd28458a08c150b7cbf1873e59af74588138",
           "rust_toolchain": "nightly-2026-09-17", "llbc_has_errors": False,
           "commands": records}
(out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
print("reduction extraction passed")
