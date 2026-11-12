#!/usr/bin/env python3
"""Check that the compiled dispatch extraction only adapts module imports."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/verify-dispatch")
RAW = DIRECTORY / "Arithmetic"
RUNTIME = Path("bridge/Arithmetic/VerifyDispatchRuntime.lean")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(root=ROOT, types=False):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    expected = {str(RAW / name) for name in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")}
    expected.update(str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log"))
    artifacts = receipt["artifacts"]
    if (receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False or
            len(artifacts) != len(expected) or {item["path"] for item in artifacts} != expected):
        raise ValueError("incomplete dispatch extraction receipt")
    for item in artifacts:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("raw dispatch artifact drift: " + item["path"])

    if sha(root / RUNTIME) != receipt["scoped_runtime_sha256"]:
        raise ValueError("scoped dispatch runtime mismatch")
    template = (root / RAW / "FunsExternal_Template.lean").read_bytes()
    if re.findall(rb"(?m)^axiom\s+(\S+)", template) != [b"core.num.U64.div_ceil"]:
        raise ValueError("dispatch external declaration set changed")

    raw = RAW / ("Types.lean" if types else "Funs.lean")
    active = Path("bridge/Arithmetic") / ("VerifyDispatchTypes.lean" if types else "VerifyDispatchGenerated.lean")
    original = (root / raw).read_bytes()
    projected = original
    if not types:
        for before, after in (
            (b"public import Arithmetic.Types\n", b"public import Arithmetic.VerifyDispatchTypes\n"),
            (b"public import Arithmetic.FunsExternal\n", b"public import Arithmetic.VerifyDispatchRuntime\n"),
        ):
            if projected.count(before) != 1:
                raise ValueError("unexpected dispatch import")
            projected = projected.replace(before, after)
    if (root / active).read_bytes() != projected:
        raise ValueError("compiled dispatch declarations differ")

    declarations = re.findall(rb"(?m)^(?:def|impl_def|structure)\s+(\S+)", original)
    if len(declarations) != (1 if types else 4):
        raise ValueError("unexpected dispatch declaration count")
    return {
        "raw_generated_file": str(raw),
        "raw_file_sha256": sha(root / raw),
        "compiled_projection": str(active),
        "projection_file_sha256": sha(root / active),
        "source_declarations_retained_verbatim": len(declarations),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name.decode() for name in declarations],
        "native_source_edited": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--types", action="store_true")
    print(json.dumps(check(types=parser.parse_args().types), indent=2))
