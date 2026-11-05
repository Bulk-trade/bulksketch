#!/usr/bin/env python3
"""Confirm that the independent axiom policy rejects a deliberately invalid certificate.

The temporary fixture is outside the production proof namespace/import roots.
It is never counted as a proof and does not edit native source or frozen specs.
"""
from pathlib import Path
import json
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "audit/results"
ENV = dict(os.environ, LEAN_NUM_THREADS="2")
CHAIN = "leanprover/lean4:v4.35.0"


def main():
    source = AUDIT / "negative/Forbidden.lean"
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text("namespace AuditNegative\naxiom forbiddenApplicationCorrectness : False\ntheorem rejectMe : False := forbiddenApplicationCorrectness\nend AuditNegative\n")
    output = ROOT / ".lake/build/lib/lean/audit/results/negative/Forbidden.olean"
    output.parent.mkdir(parents=True, exist_ok=True)
    command = ["elan", "run", CHAIN, "lake", "env", "lean", str(source), "-o", str(output)]
    compiled = subprocess.run(command, cwd=ROOT, env=ENV, stdin=subprocess.DEVNULL,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=30)
    if compiled.returncode:
        raise RuntimeError("negative fixture did not elaborate: " + compiled.stdout)
    export = AUDIT / "negative/forbidden.export.ndjson"
    with export.open("w") as out:
        result = subprocess.run(["elan", "run", CHAIN, "lake", "env", "leanexport",
                                 "audit.results.negative.Forbidden", "--", "AuditNegative.rejectMe"],
                                cwd=ROOT, env=ENV, stdin=subprocess.DEVNULL, stdout=out,
                                stderr=subprocess.PIPE, text=True, timeout=30)
    if result.returncode:
        raise RuntimeError("negative fixture export failed: " + result.stderr)
    config = AUDIT / "negative/nanoda.json"
    config.write_text(json.dumps({"use_stdin": False, "export_file_path": str(export),
                                 "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
                                 "unpermitted_axiom_hard_error": True, "num_threads": 2,
                                 "nat_extension": True, "string_extension": True}, indent=2) + "\n")
    prefix = Path(subprocess.check_output(["elan", "run", CHAIN, "lean", "--print-prefix"], text=True).strip())
    checked = subprocess.run([str(prefix / "bin/nanoda_bin"), str(config)], cwd=ROOT,
                             env=ENV, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True, timeout=30)
    (AUDIT / "negative/nanoda.log").write_text(checked.stdout)
    if checked.returncode == 0 or "forbiddenApplicationCorrectness" not in checked.stdout:
        raise RuntimeError("axiom policy did not demonstrably reject the forbidden premise: " + checked.stdout)
    result = {"status": "expected_rejection_confirmed", "checker_exit_code": checked.returncode,
              "forbidden_axiom": "AuditNegative.forbiddenApplicationCorrectness",
              "fixture_in_production_proof_roots": False}
    shadow = AUDIT / "negative/challenge-shadow"
    shadow.mkdir(exist_ok=True)
    for filename in ["lean-toolchain", "lakefile.toml", "BulksketchProofs.lean"]:
        shutil.copy2(ROOT / filename, shadow / filename)
    for path in (ROOT / "BulksketchProofs").rglob("*.lean"):
        destination = shadow / path.relative_to(ROOT)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, destination)
    reduction = shadow / "BulksketchProofs/Field/Reduction.lean"
    replacement = '''axiom generated_remainder_high_bits (low high : BitVec 64) (i : Nat)
    (hi : 64 ≤ i) :
    ((BulksketchProofs.Generated.reduceGf64 low high).setWidth 128).getLsbD i = false

end BulksketchProofs.Field'''
    altered, count = re.subn(r"theorem generated_remainder_high_bits\b[\s\S]*?end BulksketchProofs\.Field",
                             lambda _: replacement, reduction.read_text())
    if count != 1:
        raise RuntimeError("negative challenge fixture could not locate the selected root")
    reduction.write_text(altered)
    rejected = subprocess.run(["elan", "run", CHAIN, "lake", "build", "BulksketchProofs.Audit"],
                              cwd=shadow, env=ENV, stdin=subprocess.DEVNULL,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=60)
    (AUDIT / "negative/challenge-shadow.log").write_text(rejected.stdout)
    if rejected.returncode == 0 or "challenge solution must be a theorem" not in rejected.stdout:
        raise RuntimeError("same-type axiom replacement was not demonstrably rejected: " + rejected.stdout)
    result["same_type_challenge_axiom_replacement"] = {
        "status": "expected_rejection_confirmed", "exit_code": rejected.returncode,
        "root": "BulksketchProofs.Field.generated_remainder_high_bits",
        "native_or_production_proof_modified": False}
    (AUDIT / "negative-fixtures.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
