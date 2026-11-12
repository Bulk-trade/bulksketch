#!/usr/bin/env python3
"""Single fail-closed entry point for current native-only proof milestones."""
from pathlib import Path
import json
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "audit/results/overall-verification.json"


def main():
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps({"status": "running"}) + "\n")
    with subprocess.Popen(["git", "cat-file", "--batch"], cwd=ROOT.parents[1],
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as blobs:
        for entry in subprocess.check_output(["git", "ls-files", "--stage", "-z"], cwd=ROOT.parents[1]).split(b"\0"):
            if not entry:
                continue
            metadata, path = entry.split(b"\t", 1)
            mode, oid, stage = metadata.split()
            if mode == b"160000":
                continue
            blobs.stdin.write(oid + b"\n")
            blobs.stdin.flush()
            header = blobs.stdout.readline().split()
            if len(header) != 3 or header[:2] != [oid, b"blob"]:
                raise RuntimeError("invalid staged publication blob")
            contents = blobs.stdout.read(int(header[2]))
            if blobs.stdout.read(1) != b"\n":
                raise RuntimeError("invalid staged publication framing")
            if stage != b"0" or re.search(
                    rb"/(?:Users|home)/[^/\s\"<>]+|/(?:private/)?var/folders/[^/\s\"<>]+", contents):
                message = "unsafe staged publication file: " + path.decode(errors="replace")
                OUTPUT.write_text(json.dumps({"status": "failed", "error": message}) + "\n")
                raise SystemExit(message)
    stages = []
    for script in ["verify.py", "verify_bridge.py", "check_negative_fixtures.py",
                   "check_replay_fixtures.py", "check_projection_fixtures.py",
                   "check_variant_fixtures.py"]:
        start = time.monotonic()
        result = subprocess.run(["python3", str(ROOT / "scripts" / script)], cwd=ROOT)
        stages.append({"script": script, "exit_code": result.returncode,
                       "elapsed_seconds": time.monotonic() - start})
        if result.returncode:
            OUTPUT.write_text(json.dumps({"status": "failed", "stages": stages}, indent=2) + "\n")
            raise SystemExit(result.returncode)
    core = json.loads((ROOT / "audit/results/verification.json").read_text())
    bridge = json.loads((ROOT / "bridge/audit/results/verification.json").read_text())
    if core["status"] != "passed" or bridge["status"] != "passed":
        raise RuntimeError("missing successful proof stage")
    summary = {"status": "passed", "stages": stages,
               "native_executable_declarations_in_scope": core["native_executable_declarations_in_scope"],
               "core_handwritten_theorem_declarations": core["handwritten_theorem_declarations"],
               "checked_generated_body_refinements": bridge["checked_generated_body_refinements"],
               "checked_stateful_llbc_refinements": bridge["checked_stateful_llbc_refinements"],
               "matched_frozen_challenges": core["frozen_challenges_matched"] + bridge["frozen_challenges_matched"],
               "whole_native_coverage_achieved": False,
               "note": "Verified current proof milestones under recorded source/translator/runtime assumptions. Full native contracts/expanded-body closure remain open; no coverage percentage claimed."}
    OUTPUT.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        OUTPUT.write_text(json.dumps({"status": "failed", "error": str(error)}, indent=2) + "\n")
        raise
