#!/usr/bin/env python3
"""Check the exact original dense-normalization declarations and imports."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/dense-normalization")
RAW = DIRECTORY / "Normalized"
ACTIVE_TYPES = Path("bridge/Arithmetic/DenseNormalizationTypes.lean")
ACTIVE_FUNS = Path("bridge/Arithmetic/DenseNormalizationGenerated.lean")
ORIGINAL_IMPORTS = b"public import Normalized.Types\npublic import Normalized.FunsExternal\n"
ADAPTED_IMPORTS = (b"public import Arithmetic.DenseNormalizationTypes\n"
                   b"public import Arithmetic.ReversePositionRuntime\n")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(root=ROOT, types=False):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    expected = {str(RAW / name) for name in ["Types.lean", "Funs.lean", "FunsExternal_Template.lean"]}
    expected.update(str(DIRECTORY / name) for name in ["normalized.llbc", "charon.log", "aeneas.log"])
    if (receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False or
            len(receipt["artifacts"]) != len(expected) or
            {item["path"] for item in receipt["artifacts"]} != expected):
        raise ValueError("incomplete dense-normalization extraction receipt")
    for item in receipt["artifacts"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("raw dense-normalization artifact drift: " + item["path"])
    raw_types = (root / RAW / "Types.lean").read_bytes()
    raw_funs = (root / RAW / "Funs.lean").read_bytes()
    if (root / ACTIVE_TYPES).read_bytes() != raw_types:
        raise ValueError("compiled dense-normalization types differ")
    if (raw_funs.count(ORIGINAL_IMPORTS) != 1 or
            (root / ACTIVE_FUNS).read_bytes() != raw_funs.replace(ORIGINAL_IMPORTS, ADAPTED_IMPORTS)):
        raise ValueError("compiled dense-normalization declarations differ")
    original, active, source, count = ((RAW / "Types.lean", ACTIVE_TYPES, raw_types, 2) if types else
                                        (RAW / "Funs.lean", ACTIVE_FUNS, raw_funs, 9))
    declarations = re.findall(rb"(?m)^def\s+(\S+)", source)
    if len(declarations) != count:
        raise ValueError("unexpected dense-normalization declaration count")
    return {"raw_generated_file": str(original), "raw_file_sha256": sha(root / original),
            "compiled_projection": str(active), "projection_file_sha256": sha(root / active),
            "source_declarations_retained_verbatim": count,
            "shared_types_and_function_dictionary_declarations_checked": True,
            "generated_declarations": ["bulksketch." + name.decode() for name in declarations],
            "native_source_edited": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--types", action="store_true")
    print(json.dumps(check(types=parser.parse_args().types), indent=2))
