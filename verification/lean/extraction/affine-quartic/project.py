#!/usr/bin/env python3
"""Check the pinned original affine quartic and its scoped bindings."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/affine-quartic")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/AffineQuarticGenerated.lean")
RUNTIME = Path("bridge/Arithmetic/AffineQuarticRuntime.lean")
SOURCE = Path("src/decode/deg34.rs")
SELECTOR = "bulksketch::decode::deg34::affine_quartic"
METHOD = "decode.deg34.affine_quartic"
SHARED_APPLICATION = {
    "bulksketch::decode::deg34::quadratic": ("Arithmetic/CubicGenerated.lean", "BulksketchBridge.Cubic.quadratic_refines"),
    "bulksketch::decode::deg34::cubic": ("Arithmetic/CubicGenerated.lean", "BulksketchBridge.Cubic.cubic_refines"),
    "bulksketch::decode::deg34::certificate": ("Arithmetic/CertificateGenerated.lean", "BulksketchBridge.Certificate.certificate_refines"),
}
ARTIFACTS = {str(DIRECTORY / path) for path in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "Arithmetic/Funs.lean",
    "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean",
)}
NAMES = ["Shared0A.Insts.CoreCmpEq", "Shared0A.Insts.CoreCmpOrd", METHOD]
EXTERNALS = ["Shared0A.Insts.CoreCmpOrd.cmp", "core.iter.traits.iterator.Iterator.min.default",
             "core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.min",
             "core.option.Option.Insts.CoreOpsTry_traitTry.branch",
             "core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual",
             "core.slice.raw.from_ref", "decode.deg34.quadratic", "decode.deg34.cubic",
             "decode.deg34.certificate"]
HEADER = """-- Exact original-source declaration projection. Imports and scoped external bindings are adapted only.
module
public import Arithmetic.CubicGenerated
public import Arithmetic.CertificateGenerated
public import Arithmetic.AffineQuarticRuntime
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

local notation "Shared0A.Insts.CoreCmpOrd.cmp" => Aeneas.Std.AffineQuarticRuntime.sharedCmp
local notation "core.iter.traits.iterator.Iterator.min.default" => Aeneas.Std.AffineQuarticRuntime.minimum

"""


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    declarations = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        names = re.findall(r"(?m)^(?:def|impl_def|inductive|structure|abbrev)\s+(\S+)", block)
        require(len(names) == 1 and names[0] not in declarations,
                "unexpected affine declaration in " + str(path))
        declarations[names[0]] = block.strip()
    return declarations


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["status"] == "generated" and receipt["source_root"] == SELECTOR and
            receipt["llbc_has_errors"] is False and set(receipt["artifacts"]) == ARTIFACTS,
            "invalid affine quartic extraction receipt")
    for path, digest in receipt["artifacts"].items():
        require(sha(root / path) == digest, "raw affine artifact differs: " + path)
    llbc = root / DIRECTORY / "arithmetic.llbc"
    document = json.loads(llbc.read_text())
    translated = document["translated"]
    require(sha(llbc) == receipt["llbc_sha256"] and document["has_errors"] is False and
            translated["options"]["start_from"] == [SELECTOR] and
            set(translated["options"]["opaque"]) == set(SHARED_APPLICATION),
            "affine quartic LLBC root or external scope changed")
    targets = translated["target_information"]
    require(len(targets) == 1 and targets[0]["key"] == "x86_64-apple-darwin" and
            targets[0]["value"]["target_pointer_size"] == 8, "unexpected affine target")
    native = (root.parents[1] / SOURCE).read_text()
    require(hashlib.sha256(native.encode()).hexdigest() == receipt["source_sha256"],
            "frozen affine Rust source differs")
    selected = [{"Ident": [part, 0]} for part in SELECTOR.split("::")]
    roots = [fn for fn in translated["fun_decls"] if fn and fn["item_meta"]["name"] == selected]
    require(len(roots) == 1 and "Structured" in roots[0]["body"], "affine body missing from LLBC")
    span = roots[0]["item_meta"]["span"]["Untagged"]["data"]
    source = translated["files"][span["file_id"]]
    require(span["beg"] == {"line": 138, "col": 0} and span["end"] == {"line": 160, "col": 1} and
            source["name"] == {"Local": str(SOURCE)} and source["contents"] == native,
            "affine LLBC span or source contents differ")
    require(sha(root / RUNTIME) == receipt["runtime_sha256"], "scoped affine runtime differs")
    require(re.findall(r"(?m)^axiom\s+(\S+)", (root / RAW / "FunsExternal_Template.lean").read_text()) == EXTERNALS,
            "affine external declaration set changed")
    types = blocks(root / RAW / "Types.lean")
    shared_types = blocks(root / "bridge/Arithmetic/Types.lean") | blocks(root / "bridge/Arithmetic/SliceKernelTypes.lean")
    require(len(types) == 6 and all(shared_types.get(name) == block for name, block in types.items()),
            "shared affine type differs")
    require(set(receipt["opaque_application_bodies"]) == set(SHARED_APPLICATION),
            "affine application reuse changed")
    for name, (path, theorem) in SHARED_APPLICATION.items():
        generated = name.removeprefix("bulksketch::").replace("::", ".")
        declaration = blocks(root / "bridge" / path).get(generated)
        binding = receipt["opaque_application_bodies"][name]
        require(declaration is not None and binding["theorem"] == theorem and
                binding["generated_file"] == "bridge/" + path and
                hashlib.sha256(declaration.encode()).hexdigest() == binding["declaration_sha256"],
                "affine source call lacks its verified declaration: " + name)
    functions = blocks(root / RAW / "Funs.lean")
    require([name for name in functions if name in NAMES] == NAMES and
            hashlib.sha256(functions[METHOD].encode()).hexdigest() == receipt["affine_declaration_sha256"],
            "affine generated declaration set differs")
    projected = HEADER + "".join(functions[name] + "\n\n" for name in NAMES) + "end bulksketch\n"
    require((root / ACTIVE).read_text() == projected, "compiled affine projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(NAMES),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in NAMES],
        "runtime_sha256": sha(root / RUNTIME), "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
