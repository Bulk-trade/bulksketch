#!/usr/bin/env python3
"""Verify stock extraction provenance and the verbatim root-trace projection."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SETUP = importlib.util.spec_from_file_location("root_setup", ROOT / "extraction/root-setup/project.py")
setup = importlib.util.module_from_spec(SETUP)
SETUP.loader.exec_module(setup)
require, sha, declarations = setup.require, setup.sha, setup.declarations

DIRECTORY = Path("extraction/root-trace")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/RootTraceGenerated.lean")
SELECTOR = "bulksketch::decode::roots::_::trace"
OPAQUE = ["bulksketch::decode::roots::charge", "bulksketch::poly::dense::_::square_mod_into",
          "bulksketch::poly::dense::_::xor_coefficient"]
SPAN = {
    "trace": ("src/decode/roots.rs", 384, 443, "Structured"),
    "charge": ("src/decode/roots.rs", 70, 72, "Opaque"),
    "square_mod_into": ("src/poly/dense.rs", 188, 224, "Opaque"),
    "xor_coefficient": ("src/poly/dense.rs", 159, 165, "Opaque"),
    "call_once": ("src/decode/roots.rs", 394, 399, "Structured"),
}
SHARED_TYPES = {
    "Arithmetic/Types.lean": {"types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"},
    "Arithmetic/SliceKernelTypes.lean": {"backend.contract.Arithmetic", "backend.contract.BulkKernels"},
    "Arithmetic/ReconstructionTypes.lean": {"types.Stage", "types.DecodeFailure", "decode.roots.Roots",
        "decode.scratch.SplitterBasis"},
    "Arithmetic/RootSetupGenerated.lean": {"decode.roots.FactorWork"},
    "Arithmetic/WorkScheduleGenerated.lean": {"decode.work.Charge"},
    "Workmeter/Types.lean": {"types.WorkUnits", "types.WorkMeter", "types.DecodeError"},
}
ARTIFACTS = {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "replay.log", "Arithmetic/Funs.lean",
    "Arithmetic/FunsExternal_Template.lean", "Arithmetic/Types.lean",
)}
NAME = "decode.roots.Roots.trace"
CLOSURE = NAME + ".closure"
DICT = CLOSURE + ".Insts.CoreOpsFunctionFnOnceTupleArrayU6464"
FUN_NAMES = (DICT + ".call_once", DICT, NAME + "_loop0.body", NAME + "_loop0",
             NAME + "_loop1.body", NAME + "_loop1", NAME)


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["source_commit"] == setup.SOURCE and receipt["selector"] == SELECTOR
            and receipt["target"] == setup.TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["aeneas_commit"] == setup.AENEAS and receipt["charon_commit"] == setup.CHARON
            and receipt["binary_sha256"] == setup.BINARY_SHA256 and receipt["native_source_edited"] is False
            and receipt["opaque_application_bodies"] == OPAQUE and receipt["checked_exit"] == 0
            and set(receipt["files_sha256"]) == ARTIFACTS, "invalid root trace receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "root trace artifact differs: " + path)
    ch, ae, replay = (receipt[key] for key in ("charon_command", "aeneas_command", "replay"))
    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    source_root = Path(manifest.removeprefix("--manifest-path=")).parent
    require(ch[0] == parent["charon_command"][0]
            and ch[1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"]
            and ch[4].startswith("--dest-file=")
            and ch[5:10] == ["--start-from=" + SELECTOR, *("--opaque=" + name for name in OPAQUE), "--"]
            and ch[10] == manifest
            and ch[11:] == ["-p", "bulksketch", "--lib", "--locked", "--target", setup.TARGET],
            "root trace recorded Charon command differs")
    destination = Path(ch[4].removeprefix("--dest-file="))
    require(destination == source_root.parent / "bulksketch-proof-evidence-20261109-root-traversal/trace/arithmetic.llbc"
            and ae[0] == parent["aeneas_command"][0]
            and ae[1:-2] == setup.FLAGS and Path(ae[-1]) == destination
            and Path(ae[-2]) == destination.parent / "stock"
            and replay["command"] == [*ae[:-2], str(destination.parent / "replay"), ae[-1]]
            and replay["exit_code"] == 0
            and replay["input_sha256"] == sha(root / DIRECTORY / "arithmetic.llbc")
            and replay["log_sha256"] == sha(root / DIRECTORY / "replay.log")
            and replay["outputs"] == {name: sha(root / RAW / name) for name in
                                       ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")},
            "root trace checked replay differs")
    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    targets = translated["target_information"]
    require(llbc["has_errors"] is False and translated["options"]["start_from"] == [SELECTOR]
            and translated["options"]["opaque"] == OPAQUE and translated["options"]["dest_file"] == str(destination)
            and len(targets) == 1
            and targets[0]["key"] == setup.TARGET and targets[0]["value"]["target_pointer_size"] == 8,
            "root trace LLBC closure or target differs")
    expected_source = {path: sha(root.parents[1] / path) for path, *_ in SPAN.values()}
    require(receipt["source_sha256"] == expected_source, "root trace pinned source differs")
    found = {}
    for fn in translated["fun_decls"]:
        if not fn:
            continue
        meta = fn["item_meta"]
        span = meta["span"]["Untagged"]["data"]
        source = translated["files"][span["file_id"]]
        name = meta["name"][-1].get("Ident", [""])[0]
        file = source["name"].get("Local")
        if name not in SPAN or file != SPAN[name][0]:
            continue
        require(name not in found and hashlib.sha256(source["contents"].encode()).hexdigest() == expected_source[file],
                "root trace embedded source differs")
        body = fn["body"]
        found[name] = (file, span["beg"]["line"], span["end"]["line"],
                       body if isinstance(body, str) else next(iter(body)))
    require(found == SPAN, "root trace selected body or opaque call differs")
    types = declarations(root / RAW / "Types.lean")
    require(set(types) == {name for names in SHARED_TYPES.values() for name in names} | {CLOSURE},
            "root trace type set differs")
    for path, names in SHARED_TYPES.items():
        existing = declarations(root / "bridge" / path)
        require(all(types[name] == existing.get(name) for name in names), "root trace shared type differs: " + path)
    funs = declarations(root / RAW / "Funs.lean")
    parts = [types[CLOSURE]]
    for name in FUN_NAMES:
        if name in (NAME + "_loop1", NAME):
            called = NAME + ("_loop1.body" if name.endswith("_loop1") else "_loop1")
            parts.append(f'local notation "{called}" => ({called} squareModel)')
        parts.append(funs[name])
    require((root / ACTIVE).read_text() == HEADER + "\n\n".join(parts) + "\nend bulksketch\n",
            "compiled root trace projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(parts) - 2,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in (CLOSURE, *FUN_NAMES)],
        "native_source_edited": False,
    }


HEADER = """-- Exact checked source projection. See extraction/root-trace for provenance.
import Arithmetic.RootSetupGenerated
import Arithmetic.DenseCoefficientGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace Aeneas.Std.RootTraceRuntime

/-- An external application slot for the still-unbound original Dense
modular-square method. The argument is explicit and introduces no axiom. -/
abbrev ModularSquare :=
  {F K : Type} → bulksketch.field.BinaryField F → bulksketch.backend.contract.BulkKernels K F →
    Slice U64 → Slice U64 → Slice U64 → Slice U64 → Slice bulksketch.types.RawProduct →
    Result (Usize × Slice U64 × Slice bulksketch.types.RawProduct)

/-- Rust Option insertion calls the closure only when absent. The closure's
captured mutable length and the writeback of the returned borrow are
both preserved in the extracted call shape. -/
structure FnOnceWithState (F Input Output : Type) where
  call_once : F → Input → Result (Output × F)

def getOrInsertWith {T F : Type}
    (once : FnOnceWithState F Unit T) (input : Option T) (closure : F) :
    Result (T × (T → Option T) × F) := do
  match input with
  | some value => .ok (value, some, closure)
  | none =>
    let (value, next) ← once.call_once closure ()
    .ok (value, some, next)

end Aeneas.Std.RootTraceRuntime

namespace bulksketch

set_option linter.dupNamespace false
set_option linter.unusedVariables false

variable (squareModel : Aeneas.Std.RootTraceRuntime.ModularSquare)

local notation "core.ops.function.FnOnce" => Aeneas.Std.RootTraceRuntime.FnOnceWithState
local notation "core.option.Option.get_or_insert_with" => Aeneas.Std.RootTraceRuntime.getOrInsertWith
local notation "poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into" => squareModel

"""


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
