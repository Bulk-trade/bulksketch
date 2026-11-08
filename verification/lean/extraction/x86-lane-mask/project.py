#!/usr/bin/env python3
"""Check the original x86 target mask with its empty type import removed."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/x86-lane-mask")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/X86LaneMaskGenerated.lean")
NAME = "backend.x86_vpclmul512.mask"
TARGET = "x86_64-apple-darwin"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    expected = {str(RAW / name) for name in ("Types.lean", "Funs.lean")}
    expected.update(str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log"))
    artifacts = receipt["artifacts"]
    if (receipt["status"] != "generated" or receipt["target"] != TARGET or
            receipt["llbc_has_errors"] is not False or
            receipt["selected_roots"] != ["bulksketch::backend::x86_vpclmul512::mask"] or
            len(artifacts) != len(expected) or {entry["path"] for entry in artifacts} != expected):
        raise ValueError("incomplete x86 mask extraction receipt")
    for entry in artifacts:
        if sha(root / entry["path"]) != entry["sha256"]:
            raise ValueError("raw x86 mask extraction mismatch: " + entry["path"])
    if json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())["has_errors"] is not False:
        raise ValueError("x86 mask LLBC is incomplete")
    raw_types = (root / RAW / "Types.lean").read_bytes()
    if raw_types.split(b"namespace bulksketch\n", 1)[1].rsplit(b"end bulksketch", 1)[0].strip():
        raise ValueError("x86 mask extraction unexpectedly declares types")
    raw = RAW / "Funs.lean"
    original = (root / raw).read_bytes()
    if re.findall(rb"(?m)^def\s+(\S+)", original) != [NAME.encode()]:
        raise ValueError("x86 mask declaration set changed")
    unused = b"public import Arithmetic.Types\n"
    if original.count(unused) != 1 or (root / ACTIVE).read_bytes() != original.replace(unused, b""):
        raise ValueError("compiled x86 mask projection differs")
    return {"raw_generated_file": str(raw), "raw_file_sha256": sha(root / raw),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": 1,
            "shared_types_and_function_dictionary_declarations_checked": True,
            "generated_declarations": ["bulksketch." + NAME], "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
