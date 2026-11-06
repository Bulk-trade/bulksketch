#!/usr/bin/env python3
"""Reject edits to actual inverse bodies and the shared extraction boundary."""
from pathlib import Path
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("inverse_projection", ROOT / "extraction/inverse-chain/project.py")
PROJECTOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PROJECTOR)


def main():
    original = PROJECTOR.check()
    files = ["extraction/inverse-chain/receipt.json", "extraction/inverse-chain/Inverse/Funs.lean",
             "extraction/inverse-chain/Inverse/Types.lean", "bridge/Arithmetic/InverseGenerated.lean",
             "bridge/Arithmetic/Types.lean", "bridge/Arithmetic/Funs.lean"]
    cases = [
        ("compiled-body-edit", files[3], "if a = 0#u64", "if a = 1#u64", "compiled inverse projection differs"),
        ("shared-type-edit", files[4], "BITS : Result Std.U32", "BITS : Result Std.U64", "shared type mismatch"),
        ("shared-dictionary-edit", files[5], "BITS : Std.U32 := 64#u32", "BITS : Std.U32 := 63#u32", "shared dictionary/function mismatch"),
        ("raw-extraction-edit", files[1], "if a = 0#u64", "if a = 1#u64", files[1]),
    ]
    results = []
    for name, path, before, after, diagnostic in cases:
        with tempfile.TemporaryDirectory(prefix="bulksketch-inverse-provenance-") as directory:
            shadow = Path(directory)
            for file in files:
                (shadow / file).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(ROOT / file, shadow / file)
            PROJECTOR.check(shadow)
            text = (shadow / path).read_text()
            if before not in text:
                raise RuntimeError("fixture did not find mutation target: " + name)
            (shadow / path).write_text(text.replace(before, after, 1))
            try:
                PROJECTOR.check(shadow)
            except ValueError as error:
                if diagnostic not in str(error):
                    raise RuntimeError("wrong rejection for " + name + ": " + str(error)) from error
                results.append({"case": name, "status": "expected_rejection_confirmed"})
            else:
                raise RuntimeError("edited extraction boundary was accepted: " + name)
            optimized = subprocess.run([sys.executable, "-O", "-c",
                "from pathlib import Path; import runpy,sys; "
                "runpy.run_path(sys.argv[1])['check'](Path(sys.argv[2]))",
                str(ROOT / "extraction/inverse-chain/project.py"), str(shadow)],
                stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, timeout=10)
            if optimized.returncode == 0 or diagnostic not in optimized.stdout:
                raise RuntimeError("optimized Python did not reject " + name + ": " + optimized.stdout)
            results.append({"case": name + "-optimized-python", "status": "expected_rejection_confirmed"})
    summary = {"status": "passed", "verbatim_inverse_declarations": original["source_declarations_retained_verbatim"],
               "cases": results, "native_or_production_proof_modified": False}
    output = ROOT / "bridge/audit/results/projection-fixtures.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
