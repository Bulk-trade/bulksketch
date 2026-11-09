#!/usr/bin/env python3
"""Build and check the retained original Roots::enumerate_affine declaration."""
import hashlib
from pathlib import Path
import importlib.util
import json

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/root-enumerate-affine")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/RootEnumerateGenerated.lean")
SETUP = ROOT / "extraction/root-setup/project.py"
ARTIFACTS = {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "replay.log", "Arithmetic/Funs.lean",
    "Arithmetic/FunsExternal_Template.lean", "Arithmetic/Types.lean",
)}
spec = importlib.util.spec_from_file_location("root_setup", SETUP)
setup = importlib.util.module_from_spec(spec)
spec.loader.exec_module(setup)
require, sha, declarations = setup.require, setup.sha, setup.declarations
NAME = "decode.roots.Roots.enumerate_affine"
SELECTOR = "bulksketch::decode::roots::_::enumerate_affine"
OPAQUE = ["bulksketch::decode::affine::enumerate", "bulksketch::decode::roots::_::advance"]
SHARED_TYPES = {
    "Arithmetic/Types.lean": {"field.BinaryField", "field.sealed.Sealed", "types.FieldId", "types.RawProduct"},
    "Arithmetic/RebuiltLfsrTypes.lean": {"core.ops.range.RangeToInclusive"},
    "Arithmetic/SliceKernelTypes.lean": {"backend.contract.Arithmetic", "backend.contract.BulkKernels"},
    "Arithmetic/ReconstructionTypes.lean": {"decode.roots.Roots", "decode.scratch.FactorFrame",
        "decode.scratch.RowWorkspace", "decode.scratch.SplitterBasis", "types.DecodeFailure", "types.Stage"},
    "Arithmetic/WorkScheduleGenerated.lean": {"decode.work.Charge", "decode.work.WorkScheduleV1.cost.closure",
        "decode.work.number.closure"},
    "Workmeter/Types.lean": {"types.DecodeError", "types.WorkMeter", "types.WorkMeter.charge.closure",
        "types.WorkUnits"},
}
HEADER = """-- Original checked source projection for Roots::enumerate_affine.
import Arithmetic.ClosedLeafGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace Aeneas.Std.RootEnumerateRuntime

open bulksketch

/-- Explicit original affine enumeration call. -/
abbrev Enumerate := ∀ {F K : Type}, field.BinaryField F → backend.contract.BulkKernels K F →
  Slice U64 → U64 → Slice U64 → Slice U64 → Slice U64 →
    Result (core.result.Result Usize types.DecodeFailure × Slice U64 × Slice U64)

/-- Shared Rust Option view preserves the tag and payload. -/
def optionAsRef {T : Type} (value : Option T) : Result (Option T) := .ok value

end Aeneas.Std.RootEnumerateRuntime

namespace bulksketch

variable (enumerateModel : RootEnumerateRuntime.Enumerate)

local notation "decode.affine.enumerate" => enumerateModel
local notation "core.option.Option.as_ref" => RootEnumerateRuntime.optionAsRef
local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  RebuiltLfsrRuntime.inclusive

"""


def projection(root=ROOT):
    return HEADER + declarations(root / RAW / "Funs.lean")[NAME] + "\nend bulksketch\n"


def check(root=ROOT):
    runtime = root / "bridge"
    original = declarations(root / RAW / "Funs.lean")
    charge = declarations(runtime / "Arithmetic/ClosedLeafGenerated.lean")
    require(original["decode.roots.charge"] == charge["decode.roots.charge"], "charge declaration differs")
    types = declarations(root / RAW / "Types.lean")
    require(set(types) == set().union(*SHARED_TYPES.values()), "stock type set differs")
    for file, names in SHARED_TYPES.items():
        shared = declarations(runtime / file)
        require(all(types[name] == shared.get(name) for name in names), "shared type differs: " + file)
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["source_commit"] == setup.SOURCE and receipt["selector"] == SELECTOR
            and receipt["target"] == setup.TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["aeneas_commit"] == setup.AENEAS and receipt["charon_commit"] == setup.CHARON
            and receipt["binary_sha256"] == setup.BINARY_SHA256 and receipt["native_source_edited"] is False
            and receipt["opaque_application_bodies"] == OPAQUE and receipt["checked_exit"] == 0
            and set(receipt["files_sha256"]) == ARTIFACTS, "invalid root enumerate affine receipt")
    for path, digest in receipt["files_sha256"].items():
        require(sha(root / path) == digest, "root enumerate affine artifact differs: " + path)
    translated = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    require(translated["has_errors"] is False, "capture has errors")
    found = {}
    expected = {
        "enumerate_affine": ("src/decode/roots.rs", 321, 345, "Structured"),
        "advance": ("src/decode/roots.rs", 110, 127, "Opaque"),
        "enumerate": ("src/decode/affine.rs", 302, 347, "Opaque"),
        "charge": ("src/decode/roots.rs", 70, 72, "Structured"),
    }
    llbc = translated["translated"]
    targets = llbc["target_information"]
    require(llbc["options"]["start_from"] == [SELECTOR] and llbc["options"]["opaque"] == OPAQUE
            and len(targets) == 1 and targets[0]["key"] == setup.TARGET
            and targets[0]["value"]["target_pointer_size"] == 8, "selector, scope, or target differs")
    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    destination = Path(manifest.removeprefix("--manifest-path=")).parent.parent / (
        "bulksketch-proof-evidence-20261109-native-root-run/roots-enumerate-affine/arithmetic.llbc")
    ch, ae, replay = (receipt[key] for key in ("charon_command", "aeneas_command", "replay"))
    require(ch == [parent["charon_command"][0], "cargo", "--preset=aeneas", "--sysroot=default",
                    "--dest-file=" + str(destination), "--start-from=" + SELECTOR,
                    *("--opaque=" + name for name in OPAQUE), "--", manifest,
                    "-p", "bulksketch", "--lib", "--locked", "--target", setup.TARGET]
            and ae == [parent["aeneas_command"][0], *setup.FLAGS, str(destination.parent / "stock"), str(destination)]
            and replay["command"] == [*ae[:-2], str(destination.parent / "replay"), ae[-1]]
            and replay["exit_code"] == 0
            and replay["input_sha256"] == sha(root / DIRECTORY / "arithmetic.llbc")
            and replay["log_sha256"] == sha(root / DIRECTORY / "replay.log")
            and replay["outputs"] == {name: sha(root / RAW / name) for name in
                                       ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")}
            and llbc["options"]["dest_file"] == str(destination), "checked capture or replay commands differ")
    expected_source = {path: sha(root.parents[1] / path) for path, *_ in expected.values()}
    require(receipt["source_sha256"] == expected_source, "root enumeration pinned source differs")
    for fun in llbc["fun_decls"]:
        if not fun:
            continue
        meta = fun["item_meta"]
        span = meta["span"]["Untagged"]["data"]
        src = llbc["files"][span["file_id"]]
        path = src["name"].get("Local", "")
        name = meta["name"][-1].get("Ident", [""])[0]
        if name not in expected or path != expected[name][0]:
            continue
        body = fun["body"]
        kind = body if isinstance(body, str) else next(iter(body))
        require(name not in found and hashlib.sha256(src["contents"].encode()).hexdigest() == expected_source[path],
                "source differs: " + path)
        found[name] = (path, span["beg"]["line"], span["end"]["line"], kind)
    require(found == expected, "source span, body, or callback differs")
    require(projection(root) == (root / ACTIVE).read_text(), "active projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": 1,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + NAME],
        "native_source_edited": False,
    }


if __name__ == "__main__":
    import sys
    if sys.argv[1:] == ["--emit"]:
        print(projection(), end="")
    else:
        print(json.dumps(check(), indent=2))
