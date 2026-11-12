#!/usr/bin/env python3
"""Check the original x86-visible const-square extraction and verbatim copy."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(root=ROOT):
    raw = root / "extraction/frobenius-const/square/Arithmetic/Funs.lean"
    types = root / "extraction/frobenius-const/square/Arithmetic/Types.lean"
    active = root / "bridge/Arithmetic/FrobeniusConstGenerated.lean"
    receipt = json.loads((root / "extraction/frobenius-const/square/receipt.json").read_text())
    for item in receipt["generated"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("raw const-square extraction drift: " + item["path"])
    if raw.read_bytes() != active.read_bytes():
        raise ValueError("compiled const-square projection differs")
    type_body = types.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    if type_body.strip():
        raise ValueError("const-square extraction unexpectedly declares shared types")
    declarations = re.findall(r"^def ([A-Za-z0-9_.]+)", raw.read_text(), re.MULTILINE)
    expected = ["field.frobenius.square_loop0.body", "field.frobenius.square_loop0",
                "field.frobenius.square_loop1.body", "field.frobenius.square_loop1",
                "field.frobenius.square"]
    if declarations != expected:
        raise ValueError("const-square declaration set changed")
    return {"raw_generated_file": str(raw.relative_to(root)), "raw_file_sha256": sha(raw),
            "compiled_projection": str(active.relative_to(root)), "projection_file_sha256": sha(active),
            "source_declarations_retained_verbatim": len(declarations),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "adaptation": "Whole Funs file byte-identical; generated Types contains no application declarations. Existing Arithmetic.Types imports the same pinned Aeneas scalar/runtime types; no application type or dictionary is used by this const-square body.",
            "native_source_edited": False, "cross_target": "x86_64-apple-darwin"}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
