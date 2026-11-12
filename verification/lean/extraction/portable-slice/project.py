#!/usr/bin/env python3
"""Check the original square_slice and scale_xor declarations and dependencies."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = Path("extraction/portable-slice")
RAW = EXTRACTION / "Arithmetic/Funs.lean"
ACTIVE = Path("bridge/Arithmetic/PortableSliceGenerated.lean")
PREFIX = "backend.portable.Portable.Insts.BulksketchBackendContractArithmetic."
FUNCTIONS = [PREFIX + name + suffix for name in ("scale_xor", "square_slice")
             for suffix in ("_loop.body", "_loop", "")]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(source):
    body = source.split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    return re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body)


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    names = {"Funs.lean", "Types.lean", "FunsExternal_Template.lean", "TypesExternal_Template.lean"}
    expected = {str(EXTRACTION / "Arithmetic" / name) for name in names}
    if receipt["status"] != "generated" or len(receipt["generated"]) != len(expected) or \
            {item["path"] for item in receipt["generated"]} != expected:
        raise ValueError("incomplete Portable slice extraction receipt")
    for item in receipt["generated"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("raw Portable slice extraction drift: " + item["path"])
    shared_types = set(map(str.strip, blocks((root / "bridge/Arithmetic/Types.lean").read_text())))
    for block in blocks((root / EXTRACTION / "Arithmetic/Types.lean").read_text()):
        if block.strip() not in shared_types:
            raise ValueError("shared Portable slice type mismatch")
    shared = set()
    for path in ["bridge/Arithmetic/Funs.lean", "bridge/Arithmetic/PortableGenerated.lean",
                 "bridge/Arithmetic/PortableXorGenerated.lean"]:
        shared.update(block.strip() for block in blocks((root / path).read_text()))
    xor_raw = (root / "extraction/portable-xor/Arithmetic/Funs.lean").read_text()
    # The two generic std dictionary declarations are checked against the raw
    # XOR extraction. The compiled calls use that package's scoped runtime bindings.
    shared.update(block.strip() for block in blocks(xor_raw)
                  if re.search(r"^impl_def core\.", block, re.MULTILINE))
    raw = (root / RAW).read_text()
    selected = []
    selected_names = []
    for block in blocks(raw):
        match = re.search(r"^(?:impl_def|def)\s+(\S+)", block, re.MULTILINE)
        if match and match.group(1) in FUNCTIONS:
            selected.append(block)
            selected_names.append(match.group(1))
        elif block.strip() not in shared:
            raise ValueError("shared Portable slice function/dictionary mismatch")
    header = raw.split("namespace bulksketch\n", 1)[0].replace(
        "public import Arithmetic.Types\npublic import Arithmetic.FunsExternal",
        "public import Arithmetic.PortableGenerated\npublic import Arithmetic.PortableXorGenerated")
    expected_text = header + "namespace bulksketch\n\n" + "".join(selected) + "end bulksketch\n"
    if selected_names != FUNCTIONS or (root / ACTIVE).read_text() != expected_text:
        raise ValueError("compiled Portable slice projection differs")
    return {"raw_generated_file": str(RAW), "raw_file_sha256": sha(root / RAW),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": len(selected),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
