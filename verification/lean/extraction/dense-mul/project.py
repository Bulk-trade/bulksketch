#!/usr/bin/env python3
"""Check the two verbatim Dense final-reduction loop declarations."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = "extraction/dense-mul/"
GENERATED = "bridge/Arithmetic/DenseMulReductionGenerated.lean"
NAMES = ["poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop1" + suffix
         for suffix in (".body", "")]
FILES = {EXTRACTION + name for name in ("arithmetic.llbc", "charon.log", "aeneas.log",
         "Arithmetic/Funs.lean", "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean")}
HEADER = """-- Exact original final-reduction loop declarations. Imports are adapted only.
module
public import Arithmetic.MutableZipRuntime
public import Arithmetic.SliceKernelTypes
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

"""


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    return re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body)


def projection(root):
    result = []
    for block in blocks(root / (EXTRACTION + "Arithmetic/Funs.lean")):
        name = re.search(r"^(?:def|impl_def)\s+(\S+)", block, re.MULTILINE)
        if name and name.group(1) in NAMES:
            result.append((name.group(1), block))
    if [name for name, _ in result] != NAMES:
        raise ValueError("Dense reduction loop declarations changed")
    return HEADER + "".join(block for _, block in result) + "end bulksketch\n"


def check(root=ROOT):
    receipt = json.loads((root / (EXTRACTION + "receipt.json")).read_text())
    if receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False:
        raise ValueError("Dense mul extraction is incomplete")
    if len(receipt["artifacts"]) != len(FILES) or {item["path"] for item in receipt["artifacts"]} != FILES:
        raise ValueError("Dense mul artifact set changed")
    for item in receipt["artifacts"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("raw Dense mul extraction mismatch: " + item["path"])
    shared = "\n".join((root / ("bridge/Arithmetic/" + file)).read_text() for file in
                       ("Types.lean", "SliceKernelTypes.lean", "DenseNormalizationTypes.lean"))
    for block in blocks(root / (EXTRACTION + "Arithmetic/Types.lean")):
        if block.strip() not in shared:
            raise ValueError("shared Dense mul type mismatch: " + block[:120])
    if (root / GENERATED).read_text() != projection(root):
        raise ValueError("compiled Dense reduction projection differs")
    raw = EXTRACTION + "Arithmetic/Funs.lean"
    return {"raw_generated_file": raw, "raw_file_sha256": sha(root / raw),
            "compiled_projection": GENERATED, "projection_file_sha256": sha(root / GENERATED),
            "source_declarations_retained_verbatim": len(NAMES),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "generated_declarations": ["bulksketch." + name for name in NAMES],
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
