#!/usr/bin/env python3
"""Check source-linked generated body refinements under the recorded tool/runtime TCB."""
from pathlib import Path
import hashlib
import json
import os
import re
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


def run(name, args, timeout=180, cwd=BRIDGE):
    start = time.monotonic()
    try:
        result = subprocess.run(args, cwd=cwd, env=ENV, stdin=subprocess.DEVNULL,
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
        raise RuntimeError(name + " failed with exit " + str(result.returncode) + ":\n" + result.stdout[-4000:])
    return {"name": name, "command": args, "cwd": str(cwd), "exit_code": 0,
            "elapsed_seconds": time.monotonic() - start}, result.stdout


def main():
    scope = json.loads((ROOT / "scope.json").read_text())
    source = (ROOT / scope["source_repository"]).resolve()
    head = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
    inventory = json.loads((ROOT / "audit/source-inventory.json").read_text())
    for file in inventory["files"]:
        if sha(source / file["path"]) != file["sha256"]:
            raise RuntimeError("native source body drift")
    for path, expected in scope["source_build_inputs_sha256"].items():
        if sha(source / path) != expected:
            raise RuntimeError("native build input drift: " + path)
    frozen = json.loads((AUDIT / "frozen-inputs.json").read_text())
    for path, expected in frozen["files"].items():
        if sha(ROOT / path) != expected:
            raise RuntimeError("frozen bridge/source/model input drift: " + path)
    linkage = json.loads((BRIDGE / "source-linkage.json").read_text())
    runtime = ROOT / "tooling/aeneas"
    runtime_head = subprocess.check_output(["git", "-C", str(runtime), "rev-parse", "HEAD"], text=True).strip()
    if runtime_head != linkage["aeneas_commit"] or subprocess.check_output(
            ["git", "-C", str(runtime), "status", "--porcelain", "--untracked-files=no"], text=True).strip():
        raise RuntimeError("Aeneas runtime differs from its clean reviewed source pin")
    for item in linkage["extractions"]:
        if sha(ROOT / item["path"]) != item["sha256"] or \
                json.loads((ROOT / item["path"]).read_text())["has_errors"] is not False:
            raise RuntimeError("incomplete or stale native extraction")
    for item in linkage["native_generated_copies"]:
        if (ROOT / item["generated"]).read_bytes() != (ROOT / item["bridge_copy"]).read_bytes():
            raise RuntimeError("application-generated body was edited")
        if sha(ROOT / item["bridge_copy"]) != item["sha256"]:
            raise RuntimeError("generated-body linkage hash is stale")
    registry = json.loads((BRIDGE / "obligations.json").read_text())
    coverage = json.loads((ROOT / "audit/coverage.json").read_text())
    if {item["id"] for item in coverage["items"]} != {item["id"] for item in inventory["items"]}:
        raise RuntimeError("native obligation disappeared from coverage denominator")
    records = []
    result, _ = run("build-replay-loader", ["elan", "run", CHAIN, "lake", "build", "replay_export"],
                    timeout=120, cwd=ROOT)
    records.append(result)
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
    challenges = {(event["challenge"], event["theorem"]) for event in events
                  if event["kind"] == "challenge_match"}
    names = {event["theorem"] for event in roots}
    expected = {(item["challenge"], item["theorem"]) for item in registry["challenges"]}
    if not expected or challenges != expected or not {item[1] for item in challenges} <= names:
        raise RuntimeError("bridge challenge omitted from axiom/export roots")
    summaries = [event for event in events if event["kind"] == "summary"]
    if len(summaries) != 1 or summaries[0]["public_theorems"] != len(roots) or \
            summaries[0]["matched_challenges"] != len(expected):
        raise RuntimeError("incomplete bridge theorem/challenge audit")
    items = {item["id"]: item for item in coverage["items"]}
    source_items = {item["id"]: item for item in inventory["items"]}
    refined = {entry["native_item_id"]: entry for entry in registry["refinements"]}
    evidence = {item["id"] for item in coverage["items"]
                if item.get("generated_body_refinement_evidence")}
    if len(refined) != len(registry["refinements"]) or evidence != set(refined):
        raise RuntimeError("unregistered or missing generated-body coverage evidence")
    if coverage["proof_progress"]["checked_generated_body_refinements_under_recorded_TCB"] != len(refined):
        raise RuntimeError("stale generated-body coverage summary")
    copies = {item["bridge_copy"] for item in linkage["native_generated_copies"]}
    for native_id, entry in refined.items():
        item = items[native_id]
        recorded = item["generated_body_refinement_evidence"]
        match = next((event for event in events if event["kind"] == "challenge_match" and
                      event["challenge"] == entry["challenge"] and event["theorem"] == entry["theorem"]), None)
        if source_items[native_id]["kind"] not in {"function", "method", "trait_default"} or \
                entry["source_linkage"] != "bridge/source-linkage.json" or \
                entry["source_line_span_sha256"] != source_items[native_id]["source_line_span_sha256"] or \
                item["source_line_span_sha256"] != source_items[native_id]["source_line_span_sha256"] or \
                match is None or entry["generated_declaration"] not in match["referenced_constants"] or \
                recorded["theorem"] != entry["theorem"] or \
                recorded["scope"] != entry["scope"] or \
                recorded["source_linkage"] != entry["source_linkage"] or \
                recorded["registry"] != "bridge/obligations.json" or \
                recorded["verification"] != "bridge/audit/results/verification.json" or \
                not entry["generated_files"] or not set(entry["generated_files"]) <= copies:
            raise RuntimeError("coverage claim lacks exact source/generated/challenge linkage: " + native_id)
        association = {"native_item_id": native_id,
                       "generated_declaration": entry["generated_declaration"],
                       "generated_file": entry["generated_file"]}
        declaration = entry["generated_declaration"].removeprefix("bulksketch.")
        if association not in linkage["source_definitions"] or \
                entry["generated_file"] not in entry["generated_files"] or \
                not re.search(r"^def\s+" + re.escape(declaration) + r"(?=\s|\(|\{)",
                              (ROOT / entry["generated_file"]).read_text(), re.MULTILINE):
            raise RuntimeError("generated declaration is not bound to the source-linked file: " + native_id)
    for event in roots:
        if set(event["axioms"]) - set(scope["permitted_axioms"]):
            raise RuntimeError("nonstandard bridge axiom")
    (RESULTS / "axioms.json").write_text(json.dumps(events, indent=2) + "\n")
    export = RESULTS / "bridge.export.ndjson"
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
    selector = RESULTS / "core-literal-selector.export.ndjson"
    selector_args = ["elan", "run", CHAIN, "lake", "env", "leanexport", "BulksketchBridge", "--",
                     "String.ofList", "Char.ofNat"]
    with selector.open("w") as out, (RESULTS / "literal-selector.stderr.log").open("w") as err:
        result = subprocess.run(selector_args, cwd=BRIDGE, env=ENV, stdin=subprocess.DEVNULL,
                                stdout=out, stderr=err, timeout=120)
    if result.returncode:
        raise RuntimeError("core literal selector export failed")
    prelude = RESULTS / "core-literal-prelude.export.ndjson"
    result, _ = run("project-core-literal-prelude", ["python3", str(ROOT / "scripts/project_core_prelude.py"),
        "--selector", str(selector), "--main", str(export), "--output", str(prelude)])
    result["selector_sha256"] = sha(selector)
    result["prelude_sha256"] = sha(prelude)
    records.append(result)
    result, _ = run("lean-core-prelude-replay", [str(prefix / "bin/leanchecker"),
                                               "--from-export", str(prelude)], timeout=120)
    records.append(result)
    result, _ = run("lean-kernel-replay", [str(ROOT / ".lake/build/bin/replay_export"),
                                          str(prelude), str(export)], timeout=120)
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
               "runtime_commit": runtime_head,
               "checked_generated_body_refinements": [entry["label"] for entry in registry["refinements"]],
               "frozen_challenges_matched": len(challenges),
               "axioms_used": sorted({axiom for event in roots for axiom in event["axioms"]}),
               "kernel_replay_loader": {"source": "tooling/ReplayExport.lean",
                   "source_sha256": sha(ROOT / "tooling/ReplayExport.lean"),
                   "executable_sha256": sha(ROOT / ".lake/build/bin/replay_export"),
                   "purpose": "schedule implicit core string-literal dependencies; unchanged parser/kernel/replay and original main export; every declaration checked or exact checked-prelude duplicate"},
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
