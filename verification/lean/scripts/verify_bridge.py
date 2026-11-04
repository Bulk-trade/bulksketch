#!/usr/bin/env python3
"""Check actual generated WorkMeter body refinements under the recorded tool/runtime TCB."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
BRIDGE = ROOT / "bridge"
AUDIT = BRIDGE / "audit"
RESULTS = AUDIT / "results"
CHAIN = "leanprover/lean4:v4.35.0"
ENV = dict(os.environ, CI="1", MATHLIB_NO_CACHE_ON_UPDATE="1", LEAN_NUM_THREADS="2")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(name, args, timeout=180):
    start = time.monotonic()
    try:
        result = subprocess.run(args, cwd=BRIDGE, env=ENV, stdin=subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, timeout=timeout)
    except subprocess.TimeoutExpired as error:
        output = error.stdout or ""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
        (RESULTS / (name + ".log")).write_text(output)
        raise
    (RESULTS / (name + ".log")).write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(name + " failed:\n" + result.stdout[-4000:])
    return {"name": name, "command": args, "exit_code": 0,
            "elapsed_seconds": time.monotonic() - start}, result.stdout


def main():
    scope = json.loads((ROOT / "scope.json").read_text())
    source = (ROOT / scope["source_repository"]).resolve()
    head = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
    inventory = json.loads((ROOT / "audit/source-inventory.json").read_text())
    for file in inventory["files"]:
        if sha(source / file["path"]) != file["sha256"]:
            raise RuntimeError("native source body drift")
    frozen = json.loads((AUDIT / "frozen-inputs.json").read_text())
    for path, expected in frozen["files"].items():
        if sha(ROOT / path) != expected:
            raise RuntimeError("frozen bridge/source/model input drift: " + path)
    linkage = json.loads((BRIDGE / "source-linkage.json").read_text())
    for item in linkage["native_generated_copies"]:
        if (ROOT / item["generated"]).read_bytes() != (ROOT / item["bridge_copy"]).read_bytes():
            raise RuntimeError("application-generated body was edited")
    records = []
    result, _ = run("build", ["elan", "run", CHAIN, "lake", "build",
                                "BulksketchBridge", "BulksketchBridge.Audit"], timeout=1200)
    records.append(result)
    result, output = run("axioms-and-challenges", ["elan", "run", CHAIN, "lake", "env",
                                                  "lean", "BulksketchBridge/Audit.lean"])
    records.append(result)
    events = []
    for line in output.splitlines():
        start = line.find('{"')
        if start >= 0: events.append(json.loads(line[start:]))
    roots = [event for event in events if event["kind"] == "theorem_axioms"]
    challenges = {event["theorem"] for event in events if event["kind"] == "challenge_match"}
    names = {event["theorem"] for event in roots}
    if len(challenges) != 3 or not challenges <= names:
        raise RuntimeError("bridge challenge omitted from axiom/export roots")
    for event in roots:
        if set(event["axioms"]) - set(scope["permitted_axioms"]):
            raise RuntimeError("nonstandard bridge axiom")
    (RESULTS / "axioms.json").write_text(json.dumps(events, indent=2) + "\n")
    export = RESULTS / "workmeter.export.ndjson"
    args = ["elan", "run", CHAIN, "lake", "env", "leanexport", "BulksketchBridge", "--"]
    args += sorted(names)
    start = time.monotonic()
    with export.open("w") as out, (RESULTS / "export.stderr.log").open("w") as err:
        result = subprocess.run(args, cwd=BRIDGE, env=ENV, stdin=subprocess.DEVNULL,
                                stdout=out, stderr=err, timeout=120)
    if result.returncode: raise RuntimeError("bridge export failed")
    records.append({"name": "export", "command": args, "exit_code": 0,
                    "sha256": sha(export), "bytes": export.stat().st_size,
                    "elapsed_seconds": time.monotonic() - start})
    prefix = Path(subprocess.check_output(["elan", "run", CHAIN, "lean", "--print-prefix"], text=True).strip())
    result, _ = run("lean-kernel-replay", [str(prefix / "bin/leanchecker"), "--silent",
                                          "--from-export", str(export)], timeout=120)
    records.append(result)
    config = {"use_stdin": False, "export_file_path": str(export),
              "permitted_axioms": scope["permitted_axioms"],
              "unpermitted_axiom_hard_error": True, "num_threads": 2,
              "nat_extension": True, "string_extension": True}
    (RESULTS / "nanoda.json").write_text(json.dumps(config, indent=2) + "\n")
    result, _ = run("independent-nanoda-replay", [str(prefix / "bin/nanoda_bin"),
                                                str(RESULTS / "nanoda.json")], timeout=120)
    records.append(result)
    summary = {"status": "passed", "source_commit": scope["source_commit"], "checkout_commit": head,
               "checked_generated_body_refinements": ["WorkMeter::new", "WorkMeter::charge"],
               "frozen_challenges_matched": 3,
               "axioms_used": sorted({axiom for event in roots for axiom in event["axioms"]}),
               "checks": records, "whole_native_coverage_achieved": False,
               "trust_boundary": "pinned Charon/Aeneas translation, concrete Rust std Option/scalar models, source/extraction-compiler correspondence, Rust compiler and machine semantics; no application axioms"}
    (RESULTS / "verification.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({key: summary[key] for key in ["status", "checked_generated_body_refinements",
        "frozen_challenges_matched", "axioms_used", "whole_native_coverage_achieved"]}, indent=2))


if __name__ == "__main__":
    RESULTS.mkdir(parents=True, exist_ok=True)
    (RESULTS / "verification.json").write_text(json.dumps({"status": "running"}) + "\n")
    try:
        main()
    except Exception as error:
        (RESULTS / "verification.json").write_text(json.dumps({"status": "failed", "error": str(error)}, indent=2) + "\n")
        raise
