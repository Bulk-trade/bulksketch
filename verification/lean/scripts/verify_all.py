#!/usr/bin/env python3
"""Single fail-closed entry point for current native-only proof milestones."""
from pathlib import Path
import json
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "audit/results/overall-verification.json"


def main():
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps({"status": "running"}) + "\n")
    stages = []
    for script in ["verify.py", "verify_bridge.py", "check_negative_fixtures.py", "check_replay_fixtures.py"]:
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
