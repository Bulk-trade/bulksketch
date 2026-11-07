#!/usr/bin/env python3
"""Reject edits to original generated bodies and shared extraction boundaries."""
from pathlib import Path
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PROJECTIONS = [
    ("inverse", "extraction/inverse-chain/project.py", "extraction/inverse-chain/receipt.json",
     "extraction/inverse-chain/Inverse/Funs.lean", "bridge/Arithmetic/InverseGenerated.lean",
     "if a = 0#u64", "if a = 1#u64", "compiled inverse projection differs", "shared type mismatch", "shared dictionary/function mismatch", []),
    ("portable", "extraction/portable-forwarding/project.py", "extraction/portable-forwarding/receipt.json",
     "extraction/portable-forwarding/Portable/Funs.lean", "bridge/Arithmetic/PortableGenerated.lean",
     "field.gf64.mul fieldBinaryFieldInst a b", "field.gf64.mul fieldBinaryFieldInst a a",
     "compiled Portable projection differs", "shared type mismatch", "shared function/dictionary mismatch", []),
    ("portable-inverse", "extraction/portable-inverse/project.py", "extraction/portable-inverse/receipt.json",
     "extraction/portable-inverse/PortableInverse/Funs.lean", "bridge/Arithmetic/PortableInverseGenerated.lean",
     "field.maps.inverse fieldBinaryFieldInst a", "field.maps.inverse fieldBinaryFieldInst 0#u64",
     "compiled Portable projection differs", "shared type mismatch", "shared function/dictionary mismatch",
     ["bridge/Arithmetic/InverseGenerated.lean", "bridge/Arithmetic/InverseUsingTypes.lean",
      "bridge/Arithmetic/InverseUsingGenerated.lean"]),
    ("wrappers", "extraction/inverse-wrappers/project.py", "extraction/inverse-wrappers/receipt.json",
     "extraction/inverse-wrappers/Arithmetic/Funs.lean", "bridge/Arithmetic/InverseUsingGenerated.lean",
     "coreopsfunctionFnT2TupleU64U64Inst.call c value", "coreopsfunctionFnT2TupleU64U64Inst.call c 0#u64",
     "compiled wrapper projection differs", "shared wrapper type mismatch", "shared wrapper function/dictionary mismatch",
     ["bridge/Arithmetic/InverseUsingTypes.lean", "bridge/Arithmetic/InverseGenerated.lean"]),
    ("frobenius", "extraction/frobenius-const/project.py", "extraction/frobenius-const/square/receipt.json",
     "extraction/frobenius-const/square/Arithmetic/Funs.lean", "bridge/Arithmetic/FrobeniusConstGenerated.lean",
     "if bit < 64#i32", "if bit < 63#i32", "compiled const-square projection differs", None, None, []),
    ("frobenius-tables", "extraction/frobenius-const/tables-lookup/project.py",
     "extraction/frobenius-const/tables-lookup/receipt.json",
     "extraction/frobenius-const/tables-lookup/Arithmetic/Funs.lean",
     "bridge/Arithmetic/FrobeniusTablesGenerated.lean",
     "if value < 16#usize", "if value < 15#usize", "compiled Frobenius projection differs",
     None, None, ["bridge/Arithmetic/FrobeniusConstGenerated.lean"]),
    ("slice-kernels", "extraction/slice-kernels/project.py",
     "extraction/slice-kernels/multiply-linear/receipt.json",
     "extraction/slice-kernels/multiply-linear/Arithmetic/Funs.lean",
     "bridge/Arithmetic/SliceKernelGenerated.lean",
     "ok (false, _dst, _raw)", "ok (true, _dst, _raw)", "compiled slice body projection differs",
     None, None, ["bridge/Arithmetic/SliceKernelTypes.lean"]),
]


def main():
    results = []
    originals = {}
    for label, checker, receipt_path, raw_path, active_path, before, after, changed, type_error, dictionary_error, extra_files in PROJECTIONS:
        spec = importlib.util.spec_from_file_location(label + "_projection", ROOT / checker)
        projector = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(projector)
        originals[label] = projector.check()["source_declarations_retained_verbatim"]
        receipt = json.loads((ROOT / receipt_path).read_text())
        files = [receipt_path, active_path, "bridge/Arithmetic/Types.lean", "bridge/Arithmetic/Funs.lean"]
        files += [item["path"] for item in receipt["generated"]] + extra_files
        cases = [
            ("compiled-body-edit", active_path, before, after, changed),
            ("raw-extraction-edit", raw_path, before, after, raw_path),
        ]
        if type_error:
            cases += [
                ("shared-type-edit", "bridge/Arithmetic/Types.lean", "BITS : Result Std.U32", "BITS : Result Std.U64", type_error),
                ("shared-dictionary-edit", "bridge/Arithmetic/Funs.lean", "BITS : Std.U32 := 64#u32", "BITS : Std.U32 := 63#u32", dictionary_error),
            ]
        if label == "wrappers":
            cases.append(("compiled-type-edit", "bridge/Arithmetic/InverseUsingTypes.lean",
                          "  T2\n", "  T1\n", "compiled wrapper type projection differs"))
        if label == "frobenius":
            cases.append(("raw-type-edit", "extraction/frobenius-const/square/Arithmetic/Types.lean",
                          "\nend bulksketch", "\ndef shadowType := Unit\nend bulksketch",
                          "raw const-square extraction drift"))
        if label == "frobenius-tables":
            cases.append(("shared-square-edit", "bridge/Arithmetic/FrobeniusConstGenerated.lean",
                          "if bit < 64#i32", "if bit < 63#i32", "shared Frobenius declaration drift"))
        if label == "slice-kernels":
            cases.append(("compiled-dictionary-edit", "bridge/Arithmetic/SliceKernelTypes.lean",
                          "structure backend.contract.Arithmetic", "structure changed.Arithmetic",
                          "compiled slice type projection differs"))
        for name, path, before, after, diagnostic in cases:
            name = label + "/" + name
            with tempfile.TemporaryDirectory(prefix="bulksketch-provenance-") as directory:
                shadow = Path(directory)
                for file in files:
                    (shadow / file).parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(ROOT / file, shadow / file)
                projector.check(shadow)
                text = (shadow / path).read_text()
                if before not in text:
                    raise RuntimeError("fixture did not find mutation target: " + name)
                (shadow / path).write_text(text.replace(before, after, 1))
                try:
                    projector.check(shadow)
                except ValueError as error:
                    if diagnostic not in str(error):
                        raise RuntimeError("wrong rejection for " + name + ": " + str(error)) from error
                    results.append({"case": name, "status": "expected_rejection_confirmed"})
                else:
                    raise RuntimeError("edited extraction boundary was accepted: " + name)
                optimized = subprocess.run([sys.executable, "-O", "-c",
                    "from pathlib import Path; import runpy,sys; "
                    "runpy.run_path(sys.argv[1])['check'](Path(sys.argv[2]))",
                    str(ROOT / checker), str(shadow)],
                    stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    text=True, timeout=10)
                if optimized.returncode == 0 or diagnostic not in optimized.stdout:
                    raise RuntimeError("optimized Python did not reject " + name + ": " + optimized.stdout)
                results.append({"case": name + "-optimized-python", "status": "expected_rejection_confirmed"})
    summary = {"status": "passed", "verbatim_inverse_declarations": originals["inverse"],
               "verbatim_declarations_by_projection": originals,
               "cases": results, "native_or_production_proof_modified": False}
    output = ROOT / "bridge/audit/results/projection-fixtures.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
