#!/usr/bin/env python3
"""Verify stock extraction provenance and the verbatim root-divide projection."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SETUP = importlib.util.spec_from_file_location("root_setup", ROOT / "extraction/root-setup/project.py")
setup = importlib.util.module_from_spec(SETUP)
SETUP.loader.exec_module(setup)
require, sha, declarations = setup.require, setup.sha, setup.declarations

DIRECTORY = Path("extraction/root-divide")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/RootDivideGenerated.lean")
SELECTOR = "bulksketch::decode::roots::_::divide"
OPAQUE = ["bulksketch::decode::roots::charge", "bulksketch::poly::dense::_::exact_divide_into"]
SPAN = {
    "divide": ("src/decode/roots.rs", 444, 490, "Structured"),
    "charge": ("src/decode/roots.rs", 70, 72, "Opaque"),
    "exact_divide_into": ("src/poly/dense.rs", 98, 111, "Opaque"),
    "stage": ("src/decode/roots.rs", 99, 109, "Structured"),
}
SHARED_TYPES = {
    "Arithmetic/Types.lean": {"types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"},
    "Arithmetic/SliceKernelTypes.lean": {"backend.contract.Arithmetic", "backend.contract.BulkKernels"},
    "Arithmetic/ReconstructionTypes.lean": {"types.Stage", "types.DecodeFailure", "decode.roots.Roots",
        "decode.scratch.SplitterBasis", "decode.scratch.FactorFrame"},
    "Arithmetic/RootSetupGenerated.lean": {"decode.roots.FactorWork"},
    "Arithmetic/WorkScheduleGenerated.lean": {"decode.work.Charge"},
    "Workmeter/Types.lean": {"types.WorkUnits", "types.WorkMeter", "types.DecodeError"},
}
ARTIFACTS = {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "replay.log", "Arithmetic/Funs.lean",
    "Arithmetic/FunsExternal_Template.lean", "Arithmetic/Types.lean",
)}
NAME = "decode.roots.Roots.divide"


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["source_commit"] == setup.SOURCE and receipt["selector"] == SELECTOR
            and receipt["target"] == setup.TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["aeneas_commit"] == setup.AENEAS and receipt["charon_commit"] == setup.CHARON
            and receipt["binary_sha256"] == setup.BINARY_SHA256 and receipt["native_source_edited"] is False
            and receipt["opaque_application_bodies"] == OPAQUE and receipt["checked_exit"] == 0
            and set(receipt["files_sha256"]) == ARTIFACTS, "invalid root divide receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "root divide artifact differs: " + path)
    ch, ae, replay = (receipt[key] for key in ("charon_command", "aeneas_command", "replay"))
    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    source_root = Path(manifest.removeprefix("--manifest-path=")).parent
    require(ch[0] == parent["charon_command"][0]
            and ch[1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"]
            and ch[4].startswith("--dest-file=")
            and ch[5:9] == ["--start-from=" + SELECTOR, *("--opaque=" + name for name in OPAQUE), "--"]
            and ch[9] == manifest
            and ch[10:] == ["-p", "bulksketch", "--lib", "--locked", "--target", setup.TARGET],
            "root divide recorded Charon command differs")
    destination = Path(ch[4].removeprefix("--dest-file="))
    require(destination == source_root.parent / "bulksketch-proof-evidence-20261109-root-traversal/divide/arithmetic.llbc"
            and ae[0] == parent["aeneas_command"][0]
            and ae[1:-2] == setup.FLAGS and Path(ae[-1]) == destination
            and Path(ae[-2]) == destination.parent / "stock"
            and replay["command"] == [*ae[:-2], str(destination.parent / "replay"), ae[-1]]
            and replay["exit_code"] == 0
            and replay["input_sha256"] == sha(root / DIRECTORY / "arithmetic.llbc")
            and replay["log_sha256"] == sha(root / DIRECTORY / "replay.log")
            and replay["outputs"] == {name: sha(root / RAW / name) for name in
                                       ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")},
            "root divide checked replay differs")
    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    targets = translated["target_information"]
    require(llbc["has_errors"] is False and translated["options"]["start_from"] == [SELECTOR]
            and translated["options"]["opaque"] == OPAQUE and translated["options"]["dest_file"] == str(destination)
            and len(targets) == 1
            and targets[0]["key"] == setup.TARGET and targets[0]["value"]["target_pointer_size"] == 8,
            "root divide LLBC closure or target differs")
    expected_source = {path: sha(root.parents[1] / path) for path, *_ in SPAN.values()}
    require(receipt["source_sha256"] == expected_source, "root divide pinned source differs")
    found = {}
    option = []
    for fn in translated["fun_decls"]:
        if not fn:
            continue
        meta = fn["item_meta"]
        span = meta["span"]["Untagged"]["data"]
        source = translated["files"][span["file_id"]]
        name = meta["name"][-1].get("Ident", [""])[0]
        file = source["name"].get("Local")
        if name == "as_ref" and file == "/rustc/library/core/src/option.rs":
            option.append((span["beg"], span["end"], fn["body"]))
        if name not in SPAN or file != SPAN[name][0]:
            continue
        require(name not in found and hashlib.sha256(source["contents"].encode()).hexdigest() == expected_source[file],
                "root divide embedded source differs")
        body = fn["body"]
        found[name] = (file, span["beg"]["line"], span["end"]["line"],
                       body if isinstance(body, str) else next(iter(body)))
    require(found == SPAN, "root divide selected body or opaque call differs")
    require(option == [({"line": 743, "col": 4}, {"line": 743, "col": 44}, "Opaque")],
            "root divide shared option source differs")
    types = declarations(root / RAW / "Types.lean")
    require(set(types) == {name for names in SHARED_TYPES.values() for name in names},
            "root divide type set differs")
    for path, names in SHARED_TYPES.items():
        existing = declarations(root / "bridge" / path)
        require(all(types[name] == existing.get(name) for name in names), "root divide shared type differs: " + path)
    funs = declarations(root / RAW / "Funs.lean")
    prior = declarations(root / "bridge/Arithmetic/ClosedLeafGenerated.lean")
    require(funs["decode.roots.Roots.stage"] == prior["decode.roots.Roots.stage"],
            "root divide shared stage differs")
    externals = (root / RAW / "FunsExternal_Template.lean").read_text()
    require("axiom core.option.Option.as_ref {T : Type _} : Option T → Result (Option T)" in externals,
            "root divide shared option signature differs")
    require("""axiom poly.Dense.Insts.BulksketchPolyPolynomial.exact_divide_into
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice
    types.RawProduct → Result ((Option Std.Usize) × (Slice Std.U64) ×
    (Slice Std.U64) × (Slice types.RawProduct))""" in externals,
            "root divide exact division callee signature differs")
    require("""axiom decode.roots.charge
  :
  types.WorkMeter → decode.work.Charge → Result ((core.result.Result Unit
    types.DecodeError) × types.WorkMeter)""" in externals,
            "root divide charge signature differs")
    require((root / ACTIVE).read_text() == HEADER + funs[NAME] + "\n\nend bulksketch\n",
            "compiled root divide projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": 1,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + NAME],
        "native_source_edited": False,
    }


HEADER = """-- Exact checked source projection. See extraction/root-divide for provenance.
import Arithmetic.RootSetupGenerated

open Aeneas Aeneas.Std Result Error

namespace Aeneas.Std.RootDivideRuntime

abbrev ExactDivide := ∀ {F K : Type}, bulksketch.field.BinaryField F →
    bulksketch.backend.contract.BulkKernels K F →
    Slice U64 → Slice U64 → Slice U64 → Slice U64 → Slice bulksketch.types.RawProduct →
    Result (Option Usize × Slice U64 × Slice U64 × Slice bulksketch.types.RawProduct)

/-- The scoped shared affine basis view is read-only. -/
def sharedOption {T : Type} (value : Option T) : Result (Option T) := .ok value

end Aeneas.Std.RootDivideRuntime

namespace bulksketch

variable (exactDivision : Aeneas.Std.RootDivideRuntime.ExactDivide)
local notation "poly.Dense.Insts.BulksketchPolyPolynomial.exact_divide_into" => exactDivision
local notation "core.option.Option.as_ref" => Aeneas.Std.RootDivideRuntime.sharedOption

"""


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
