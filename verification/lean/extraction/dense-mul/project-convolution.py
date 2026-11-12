#!/usr/bin/env python3
"""Check the exact original convolution loops, method and clone declarations."""
import json
from pathlib import Path
import re
import runpy

reduction = runpy.run_path(str(Path(__file__).with_name("project.py")))
ROOT = reduction["ROOT"]
GENERATED = "bridge/Arithmetic/DenseMulConvolutionGenerated.lean"
PREFIX = "poly.Dense.Insts.BulksketchPolyPolynomial.mul_into"
CLONE = "types.RawProduct.Insts.CoreCloneClone"
DEFAULT = "types.RawProduct.Insts.CoreDefaultDefault.default"
NAMES = [CLONE + ".clone", CLONE] + [PREFIX + suffix for suffix in
    ("_loop0_loop0.body", "_loop0_loop0", "_loop0.body", "_loop0", "")]
HEADER = """-- Exact original Dense convolution declarations. Imports are adapted only.
module
public import Arithmetic.DenseMulReductionGenerated
public import Arithmetic.DenseNormalizationGenerated
public import Arithmetic.OddRecurrenceGenerated
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

"""


def projection(root):
    retained = []
    shared_default = (root / "bridge/Arithmetic/OddRecurrenceGenerated.lean").read_text()
    shared_normalize = (root / "bridge/Arithmetic/DenseNormalizationGenerated.lean").read_text()
    default_count = 0
    normalization_count = 0
    for block in reduction["blocks"](root / (reduction["EXTRACTION"] + "Arithmetic/Funs.lean")):
        found = re.search(r"^(?:def|impl_def)\s+(\S+)", block, re.MULTILINE)
        if found and found.group(1) in NAMES:
            retained.append((found.group(1), block))
        elif found and found.group(1) == DEFAULT:
            default_count += 1
            if block.strip() not in shared_default:
                raise ValueError("shared RawProduct default changed")
        elif found and (found.group(1) == "poly.dense.normalized_len" or
                        found.group(1).startswith("poly.dense.normalized_len.")):
            normalization_count += 1
            if block.strip() not in shared_normalize:
                raise ValueError("shared normalization declaration changed")
    if [name for name, _ in retained] != NAMES or default_count != 1 or normalization_count != 7:
        raise ValueError("Dense convolution declaration set changed")
    return HEADER + "".join(block for _, block in retained) + "end bulksketch\n"


def check(root=ROOT):
    inherited = reduction["check"](root)
    if (root / GENERATED).read_text() != projection(root):
        raise ValueError("compiled Dense convolution projection differs")
    return {"raw_generated_file": inherited["raw_generated_file"],
            "raw_file_sha256": inherited["raw_file_sha256"],
            "compiled_projection": GENERATED,
            "projection_file_sha256": reduction["sha"](root / GENERATED),
            "source_declarations_retained_verbatim": len(NAMES),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "shared_normalization_declarations_checked": 7,
            "shared_raw_default_declarations_checked": 1,
            "generated_declarations": ["bulksketch." + name for name in NAMES],
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
