#!/usr/bin/env python3
"""Check the exact native AVX-512 feature-test bodies and scoped register reads."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/x86-feature-detect")
RAW = DIRECTORY / "Arithmetic"
RUNTIME = Path("bridge/Arithmetic/X86FeatureDetectRuntime.lean")
TYPES = Path("bridge/Arithmetic/X86FeatureDetectTypes.lean")
ACTIVE = Path("bridge/Arithmetic/X86FeatureDetectGenerated.lean")
EXTERNALS = ["core.core_arch.x86.cpuid.__cpuid_count", "core.core_arch.x86.cpuid.__cpuid",
             "core.core_arch.x86.xsave._xgetbv"]
NAMES = ["backend.detect.vpclmul512_supported", "backend.x86_vpclmul512.detect"]
HEADER = """-- Exact original feature-detection declarations with scoped register observations.
import Arithmetic.X86FeatureDetectRuntime
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

section
variable (snapshot : X86FeatureDetectRuntime.Snapshot)

local notation "core.core_arch.x86.cpuid.__cpuid" => X86FeatureDetectRuntime.cpuid snapshot
local notation "core.core_arch.x86.cpuid.__cpuid_count" => X86FeatureDetectRuntime.cpuidCount snapshot
local notation "core.core_arch.x86.xsave._xgetbv" => X86FeatureDetectRuntime.xgetbv snapshot

"""


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    expected = {str(RAW / name) for name in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")}
    expected.update(str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log"))
    artifacts = receipt["artifacts"]
    if (receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False or
            receipt["target"] != "x86_64-apple-darwin" or
            len(artifacts) != len(expected) or {entry["path"] for entry in artifacts} != expected):
        raise ValueError("incomplete x86 feature extraction receipt")
    for entry in artifacts:
        if sha(root / entry["path"]) != entry["sha256"]:
            raise ValueError("raw x86 feature extraction mismatch: " + entry["path"])
    if json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())["has_errors"] is not False:
        raise ValueError("x86 feature LLBC is incomplete")
    if sha(root / RUNTIME) != receipt["runtime_sha256"]:
        raise ValueError("scoped x86 feature runtime mismatch")
    template = (root / RAW / "FunsExternal_Template.lean").read_text()
    if re.findall(r"(?m)^axiom\s+(\S+)", template) != EXTERNALS:
        raise ValueError("x86 feature external declaration set changed")
    if (root / TYPES).read_bytes() != (root / RAW / "Types.lean").read_bytes():
        raise ValueError("compiled CPUID result type differs")
    raw = RAW / "Funs.lean"
    body = (root / raw).read_text().split("namespace bulksketch\n\n", 1)[1].rsplit("end bulksketch", 1)[0]
    names = re.findall(r"(?m)^def\s+(\S+)", body)
    if names != NAMES or (root / ACTIVE).read_text() != HEADER + body + "end\n\nend bulksketch\n":
        raise ValueError("compiled x86 feature projection differs")
    return {"raw_generated_file": str(raw), "raw_file_sha256": sha(root / raw),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": len(names),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "generated_declarations": ["bulksketch." + name for name in names],
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
