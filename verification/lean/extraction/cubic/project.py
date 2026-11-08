#!/usr/bin/env python3
"""Verify the retained original cubic bodies and shared type boundary."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/cubic")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/CubicGenerated.lean")
SHARED = ["bridge/Arithmetic/Types.lean", "bridge/Arithmetic/SliceKernelTypes.lean"]
HEADER = """-- Exact original-source declaration projection. Imports are adapted only.
module
public import Arithmetic.CubeRootGenerated
public import Arithmetic.ShapeWireRuntime
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

local notation "core.bool.Bool.then_some" => CubeRootRuntime.thenSome

"""
NAMES = ["decode.deg34.OMEGA", "decode.deg34.quadratic", "decode.deg34.cubic"]
CUBE_ROOT_NAMES = ["decode.deg34.cube_root_loop.body", "decode.deg34.cube_root_loop",
                   "decode.deg34.cube_root"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    return re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body)


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    expected = {str(RAW / name) for name in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")}
    expected.update(str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log"))
    artifacts = receipt["artifacts"]
    if (receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False or
            len(artifacts) != len(expected) or {entry["path"] for entry in artifacts} != expected):
        raise ValueError("incomplete cubic extraction receipt")
    for entry in artifacts:
        if sha(root / entry["path"]) != entry["sha256"]:
            raise ValueError("raw cubic extraction mismatch: " + entry["path"])
    if json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())["has_errors"] is not False:
        raise ValueError("cubic LLBC is incomplete")
    shared = [(root / name).read_text() for name in SHARED]
    types = blocks(root / RAW / "Types.lean")
    if len(types) != 6 or any(not any(block.strip() in file for file in shared) for block in types):
        raise ValueError("shared cubic type mismatch")
    template = (root / RAW / "FunsExternal_Template.lean").read_text()
    if re.findall(r"(?m)^axiom\s+(\S+)", template) != ["core.bool.Bool.then_some", "core.option.Option.Insts.CoreOpsTry_traitTry.branch",
            "core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual",
            "core.slice.raw.from_ref"]:
        raise ValueError("cubic external declaration set changed")
    raw = RAW / "Funs.lean"
    selected = []
    names = []
    cube_root = []
    cube_root_names = []
    for block in blocks(root / raw):
        name = re.search(r"(?m)^def\s+(\S+)", block)
        if name and name.group(1) in NAMES:
            selected.append(block)
            names.append(name.group(1))
        if name and name.group(1) in CUBE_ROOT_NAMES:
            cube_root.append(block.strip())
            cube_root_names.append(name.group(1))
    shared_cube_root = blocks(root / "bridge/Arithmetic/CubeRootGenerated.lean")
    if cube_root_names != CUBE_ROOT_NAMES or cube_root != [block.strip() for block in shared_cube_root]:
        raise ValueError("shared cube root declarations differ")
    if names != NAMES or (root / ACTIVE).read_text() != HEADER + "".join(selected) + "end bulksketch\n":
        raise ValueError("compiled cubic projection differs")
    return {"raw_generated_file": str(raw), "raw_file_sha256": sha(root / raw),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": len(names),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "shared_cube_root_declarations_checked": len(cube_root_names),
            "generated_declarations": ["bulksketch." + name for name in names],
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
