#!/usr/bin/env python3
"""Check the original insertion or encoding declarations and their scoped std runtime."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = "extraction/portable-encoding"
RUNTIME = "bridge/Arithmetic/PortableEncodingRuntime.lean"
INSERT = "backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero"
ENCODE = "backend.contract.BulkKernels.encode_nonzero.default"
METHODS = {
    "insert": ("PortableInsertionGenerated", [INSERT + suffix for suffix in
        ["_loop0_loop0.body", "_loop0_loop0", "_loop0.body", "_loop0", ""]]),
    "encode": ("PortableEncodingGenerated", [ENCODE + suffix for suffix in ["_loop.body", "_loop", ""]]),
}
HEADER = """-- Exact original declarations. Only imports and scoped std bindings are adapted.
module
public import Arithmetic.PortableEncodingRuntime
public import Arithmetic.PortableGenerated
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


def check(root=ROOT, kind="insert"):
    module, expected = METHODS[kind]
    directory = f"{EXTRACTION}/{kind}"
    receipt = json.loads((root / directory / "receipt.json").read_text())
    required = {f"{directory}/{path}" for path in ["arithmetic.llbc", "charon.log", "aeneas.log",
        "Arithmetic/Types.lean", "Arithmetic/Funs.lean", "Arithmetic/FunsExternal_Template.lean"]}
    if kind == "insert":
        required.add(f"{directory}/Arithmetic/TypesExternal_Template.lean")
    if receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False:
        raise ValueError("Portable encoding extraction is incomplete")
    if len(receipt["artifacts"]) != len(required) or \
            {item["path"] for item in receipt["artifacts"]} != required:
        raise ValueError("Portable encoding raw artifact set changed")
    for item in receipt["artifacts"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("raw Portable encoding extraction mismatch: " + item["path"])
    llbc = root / directory / "arithmetic.llbc"
    if sha(llbc) != receipt["llbc_sha256"] or json.loads(llbc.read_text())["has_errors"] is not False:
        raise ValueError("Portable encoding LLBC mismatch")
    refinement = json.loads((root / directory / "refinement-receipt.json").read_text())
    if sha(root / RUNTIME) != refinement["files_sha256"][RUNTIME]:
        raise ValueError("scoped Portable encoding runtime mismatch")
    shared_types = (root / "bridge/Arithmetic/Types.lean").read_text()
    shared_types += (root / "bridge/Arithmetic/SliceKernelTypes.lean").read_text()
    for block in blocks(root / directory / "Arithmetic/Types.lean"):
        if block.strip() not in shared_types:
            raise ValueError("shared Portable encoding type mismatch: " + block[:120])
    shared_funs = (root / "bridge/Arithmetic/Funs.lean").read_text()
    shared_funs += (root / "bridge/Arithmetic/PortableGenerated.lean").read_text()
    raw = root / directory / "Arithmetic/Funs.lean"
    retained = []
    names = []
    dependencies = set()
    direct_arithmetic = {"backend.portable.Portable.Insts.BulksketchBackendContractArithmetic." + name
                         for name in ["mul", "square"]}
    for block in blocks(raw):
        declaration = re.search(r"^(?:def|impl_def)\s+(\S+)", block, re.MULTILINE)
        if not declaration:
            raise ValueError("unrecognized Portable encoding declaration")
        name = declaration.group(1)
        if name in expected:
            retained.append(block)
            names.append(name)
        elif name in direct_arithmetic or name.startswith("field.gf64."):
            if block.strip() not in shared_funs:
                raise ValueError("shared Portable arithmetic declaration mismatch: " + name)
            dependencies.add(name)
    if kind == "insert" and not direct_arithmetic <= dependencies:
        raise ValueError("Portable insertion arithmetic dependencies are incomplete")
    compiled = root / f"bridge/Arithmetic/{module}.lean"
    if names != expected or compiled.read_text() != HEADER + "".join(retained) + "end bulksketch\n":
        raise ValueError("compiled Portable encoding projection differs")
    return {"raw_generated_file": str(raw.relative_to(root)), "raw_file_sha256": sha(raw),
            "compiled_projection": str(compiled.relative_to(root)), "projection_file_sha256": sha(compiled),
            "source_declarations_retained_verbatim": len(retained),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "shared_arithmetic_declarations_checked": sorted(dependencies),
            "scoped_runtime_file": RUNTIME, "scoped_runtime_sha256": sha(root / RUNTIME),
            "generated_declarations": ["bulksketch." + name for name in names],
            "native_source_edited": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kind", choices=METHODS, default="insert")
    print(json.dumps(check(kind=parser.parse_args().kind), indent=2))
