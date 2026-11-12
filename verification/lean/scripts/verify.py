#!/usr/bin/env python3
"""Check pinned native scope, frozen statements, Lean proof closure and exported terms.

Model proof success never grants unproved Rust implementation coverage.
This is local controlled-source checking, not sandboxed Linux Comparator.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "audit"
RESULTS = AUDIT / "results"
TOOLCHAIN = "leanprover/lean4:v4.35.0"
ENV = dict(os.environ, LEAN_NUM_THREADS="2")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(name, args, timeout=180):
    start = time.monotonic()
    result = subprocess.run(args, cwd=ROOT, env=ENV, stdin=subprocess.DEVNULL,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True, timeout=timeout)
    (RESULTS / (name + ".log")).write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f"{name} exited {result.returncode}:\n{result.stdout[-4000:]}")
    return {"name": name, "command": args, "exit_code": result.returncode,
            "elapsed_seconds": time.monotonic() - start}, result.stdout


def main():
    RESULTS.mkdir(parents=True, exist_ok=True)
    scope = json.loads((ROOT / "scope.json").read_text())
    source = (ROOT / scope["source_repository"]).resolve()
    head = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
    inventory = json.loads((AUDIT / "source-inventory.json").read_text())
    if inventory["source_commit"] != scope["source_commit"]:
        raise RuntimeError("source inventory and pinned source pin disagree")
    for record in inventory["files"]:
        if digest(source / record["path"]) != record["sha256"]:
            raise RuntimeError("native source changed: " + record["path"])
    for path, expected in scope["source_build_inputs_sha256"].items():
        if digest(source / path) != expected:
            raise RuntimeError("native build/toolchain input changed: " + path)
    frozen = json.loads((AUDIT / "frozen-inputs.json").read_text())
    for path, expected in frozen["files"].items():
        if digest(ROOT / path) != expected:
            raise RuntimeError("frozen specification or extraction input changed: " + path)
    records = []
    result, _ = command("regenerate", ["python3", "extraction/regenerate.py"])
    records.append(result)
    result, _ = command("regenerate-field-tables", ["python3", "extraction/extract-field-tables.py"])
    records.append(result)
    for path, expected in frozen["files"].items():
        if digest(ROOT / path) != expected:
            raise RuntimeError("regeneration changed a frozen input: " + path)
    result, _ = command("build-proof-roots", ["elan", "run", TOOLCHAIN, "lake", "build",
                                                "BulksketchProofs", "BulksketchProofs.Audit"])
    records.append(result)
    result, output = command("axiom-and-challenge-audit", ["elan", "run", TOOLCHAIN, "lake", "env",
                                                           "lean", "BulksketchProofs/Audit.lean"])
    records.append(result)
    events = []
    for line in output.splitlines():
        start = line.find('{"')
        if start >= 0:
            events.append(json.loads(line[start:]))
    summaries = [event for event in events if event["kind"] == "summary"]
    if len(summaries) != 1 or summaries[0]["matched_challenges"] != frozen["challenge_count"]:
        raise RuntimeError("missing/incomplete frozen challenge audit")
    theorems = [event for event in events if event["kind"] == "theorem_axioms"]
    if not theorems or len(theorems) != summaries[0]["public_theorems"]:
        raise RuntimeError("missing theorem closure audit")
    challenged_roots = {event["theorem"] for event in events if event["kind"] == "challenge_match"}
    audited_roots = {event["theorem"] for event in theorems}
    if len(challenged_roots) != frozen["challenge_count"] or not challenged_roots <= audited_roots:
        raise RuntimeError("a frozen challenge root was omitted from axiom checking/export")
    for event in theorems:
        if set(event["axioms"]) - set(scope["permitted_axioms"]):
            raise RuntimeError("unpermitted axiom closure")
    coverage = json.loads((AUDIT / "coverage.json").read_text())
    if {item["id"] for item in coverage["items"]} != {item["id"] for item in inventory["items"]}:
        raise RuntimeError("native obligation disappeared from the coverage denominator")
    checked_names = {event["theorem"] for event in theorems}
    for item in coverage["items"]:
        if item["proof_status"] != "unproved":
            raise RuntimeError("complete native-contract closure remains open; narrower evidence cannot grant full implementation credit")
        for theorem in item.get("related_model_evidence", {}).get("theorems", []):
            if theorem not in checked_names:
                raise RuntimeError("coverage references an unchecked model theorem: " + theorem)
    (RESULTS / "axioms.json").write_text(json.dumps(events, indent=2) + "\n")
    proof_path = RESULTS / "all-roots.export.ndjson"
    arguments = ["elan", "run", TOOLCHAIN, "lake", "env", "leanexport", "BulksketchProofs", "--"]
    arguments += [event["theorem"] for event in theorems]
    start = time.monotonic()
    with proof_path.open("w") as out, (RESULTS / "export.stderr.log").open("w") as err:
        result = subprocess.run(arguments, cwd=ROOT, env=ENV, stdin=subprocess.DEVNULL,
                                stdout=out, stderr=err, timeout=90)
    if result.returncode or proof_path.stat().st_size == 0:
        raise RuntimeError("proof export failed")
    records.append({"name": "export", "command": arguments, "exit_code": result.returncode,
                    "elapsed_seconds": time.monotonic() - start,
                    "sha256": digest(proof_path), "bytes": proof_path.stat().st_size})
    prefix = Path(subprocess.check_output(["elan", "run", TOOLCHAIN, "lean", "--print-prefix"], text=True).strip())
    result, _ = command("lean-kernel-replay", [str(prefix / "bin/leanchecker"), "--silent",
                                                "--from-export", str(proof_path)], timeout=90)
    records.append(result)
    checker_config = {"use_stdin": False, "export_file_path": str(proof_path),
                      "permitted_axioms": scope["permitted_axioms"],
                      "unpermitted_axiom_hard_error": True, "num_threads": 2,
                      "nat_extension": True, "string_extension": True}
    (RESULTS / "nanoda.json").write_text(json.dumps(checker_config, indent=2) + "\n")
    result, _ = command("independent-nanoda-replay", [str(prefix / "bin/nanoda_bin"),
                                                      str(RESULTS / "nanoda.json")], timeout=90)
    records.append(result)
    authored = []
    for path in (ROOT / "BulksketchProofs").rglob("*.lean"):
        for match in re.finditer(r"^(private )?theorem\s+([^\s({:]+)", path.read_text(), re.MULTILINE):
            authored.append({"file": str(path.relative_to(ROOT)), "name": match[2],
                             "private": bool(match[1])})
    summary = {"source_commit": scope["source_commit"], "checkout_commit": head, "native_files_checked": len(inventory["files"]),
               "status": "passed",
               "native_executable_declarations_in_scope": inventory["summary"]["executable_declarations"],
               "handwritten_theorem_declarations": len(authored),
               "public_project_theorems_including_generated_lemmas": len(theorems),
               "frozen_challenges_matched": frozen["challenge_count"],
               "axioms_used": sorted({item for event in theorems for item in event["axioms"]}),
               "checks": records, "handwritten_theorems": authored,
               "checked_rust_implementation_refinements": 0,
               "full_implementation_coverage_achieved": False,
               "remaining_gap": "Rust semantic refinement/translator correctness and all other native obligations",
               "checking_scope": "local controlled-source exact-type/axiom audit plus exported-term Lean and independent nanoda replay; not sandboxed Linux Comparator"}
    (RESULTS / "verification.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({key: summary[key] for key in ["native_executable_declarations_in_scope",
        "handwritten_theorem_declarations", "public_project_theorems_including_generated_lemmas",
        "frozen_challenges_matched", "axioms_used", "checked_rust_implementation_refinements",
        "full_implementation_coverage_achieved"]}, indent=2))


if __name__ == "__main__":
    RESULTS.mkdir(parents=True, exist_ok=True)
    (RESULTS / "verification.json").write_text(json.dumps({"status": "running"}) + "\n")
    try:
        main()
    except Exception as error:
        (RESULTS / "verification.json").write_text(json.dumps({"status": "failed", "error": str(error)}, indent=2) + "\n")
        raise
