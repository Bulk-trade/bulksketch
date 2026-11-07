#!/usr/bin/env python3
"""Check the original table/lookup declarations and their reused dependencies."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
DIRECTORY = Path("extraction/frobenius-const/tables-lookup")
RAW = DIRECTORY / "Arithmetic/Funs.lean"
ACTIVE = Path("bridge/Arithmetic/FrobeniusTablesGenerated.lean")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(source):
    body = source.split("namespace bulksketch\n", 1)[1]
    return re.findall(r"(?ms)^/--.*?(?=^/--|^end bulksketch|\Z)", body)


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    expected = {str(DIRECTORY / "Arithmetic" / name)
                for name in ["Types.lean", "Funs.lean", "FunsExternal_Template.lean"]}
    if receipt["status"] != "generated" or receipt["target"] != "x86_64-apple-darwin" or \
            len(receipt["generated"]) != 3 or {item["path"] for item in receipt["generated"]} != expected:
        raise ValueError("incomplete Frobenius extraction receipt")
    for item in receipt["generated"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("raw Frobenius extraction drift: " + item["path"])
    types = (root / DIRECTORY / "Arithmetic/Types.lean").read_text()
    if types.split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0].strip():
        raise ValueError("unexpected application types in Frobenius extraction")
    source = (root / RAW).read_text()
    shared = [block.strip() for name in ["Funs", "FrobeniusConstGenerated"]
              for block in blocks((root / f"bridge/Arithmetic/{name}.lean").read_text())]
    selected = []
    reused = 0
    for block in blocks(source):
        name = re.search(r"^def\s+(\S+)", block, re.MULTILINE).group(1)
        if name.startswith(("field.frobenius.square", "core.num.")):
            if block.strip() not in shared:
                raise ValueError("shared Frobenius declaration drift: " + name)
            reused += 1
        else:
            selected.append(block)
    if len(selected) != 37 or reused != 6:
        raise ValueError("unexpected Frobenius declaration count")
    header = source.split("namespace bulksketch\n", 1)[0].replace(
        "public import Arithmetic.Types\npublic import Arithmetic.FunsExternal",
        "public import Arithmetic.Funs\npublic import Arithmetic.FrobeniusConstGenerated\n"
        "public import Arithmetic.FrobeniusTablesRuntime")
    projected = header + "namespace bulksketch\n\n" + "".join(selected) + "end bulksketch\n"
    if (root / ACTIVE).read_text() != projected:
        raise ValueError("compiled Frobenius projection differs")
    return {"raw_generated_file": str(RAW), "raw_file_sha256": sha(root / RAW),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": len(selected),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "shared_function_declarations": reused, "native_source_edited": False,
            "cross_target": receipt["target"]}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
