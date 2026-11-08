#!/usr/bin/env python3
"""Check the exact original Roots::leaf body and its reused verified calls."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SETUP = importlib.util.spec_from_file_location("root_setup", ROOT / "extraction/root-setup/project.py")
setup = importlib.util.module_from_spec(SETUP)
SETUP.loader.exec_module(setup)
require, sha, declarations = setup.require, setup.sha, setup.declarations

DIRECTORY = Path("extraction/root-leaf")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/RootLeafGenerated.lean")
SELECTOR = "bulksketch::decode::roots::_::leaf"
OPAQUE = ["bulksketch::decode::roots::charge", "bulksketch::decode::roots::_::advance"]
SOURCE = "src/decode/roots.rs"
DECLARATION = "decode.roots.Roots.leaf"
ARTIFACTS = {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "replay.log", "Arithmetic/Funs.lean",
    "Arithmetic/FunsExternal_Template.lean", "Arithmetic/Types.lean",
)}
SHARED_TYPES = {
    "Arithmetic/Types.lean": {"types.RawProduct", "types.FieldId", "field.sealed.Sealed",
                              "field.BinaryField"},
    "Arithmetic/SliceKernelTypes.lean": {"backend.contract.Arithmetic", "backend.contract.BulkKernels"},
    "Arithmetic/ReconstructionTypes.lean": {"types.Stage", "types.DecodeFailure", "decode.roots.Roots",
        "decode.scratch.SplitterBasis", "decode.scratch.FactorFrame", "decode.scratch.RowWorkspace"},
    "Arithmetic/WorkScheduleGenerated.lean": {"decode.work.Charge"},
    "Workmeter/Types.lean": {"types.WorkUnits", "types.WorkMeter", "types.DecodeError"},
}
BINDINGS = {
    "decode.roots.charge": "BulksketchBridge.ClosedLeafAdvance.charge_refines",
    "decode.roots.Roots.advance": "BulksketchBridge.ClosedLeafAdvance.advance_refines",
}
HEADER = """-- Exact original leaf declaration with checked shared runtime bindings.
import Arithmetic.ClosedLeafGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 2048
namespace bulksketch

"""


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["source_commit"] == setup.SOURCE and receipt["selector"] == SELECTOR
            and receipt["target"] == setup.TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["aeneas_commit"] == setup.AENEAS and receipt["charon_commit"] == setup.CHARON
            and receipt["binary_sha256"] == setup.BINARY_SHA256 and receipt["native_source_edited"] is False
            and receipt["opaque_application_bodies"] == OPAQUE and receipt["checked_exit"] == 0
            and set(receipt["files_sha256"]) == ARTIFACTS, "invalid root leaf receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "root leaf artifact differs: " + path)
    ch = receipt["charon_command"]
    ae = receipt["aeneas_command"]
    replay = receipt["replay"]
    require(Path(ch[0]).parts[-4:] == ("tooling", "charon", "bin", "charon")
            and ch[1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"]
            and ch[4].startswith("--dest-file=")
            and ch[5:9] == ["--start-from=" + SELECTOR, *("--opaque=" + name for name in OPAQUE), "--"]
            and ch[9].startswith("--manifest-path=")
            and ch[10:] == ["-p", "bulksketch", "--lib", "--locked", "--target", setup.TARGET],
            "root leaf recorded Charon command differs")
    destination = Path(ch[4].removeprefix("--dest-file="))
    require(destination.parts[-2:] == ("root-leaf", "arithmetic.llbc")
            and Path(ae[0]).parts[-6:] == ("tooling", "aeneas", "src", "_build", "default", "main.exe")
            and ae[1:-2] == setup.FLAGS and Path(ae[-1]) == destination
            and Path(ae[-2]) == destination.parent / "stock"
            and replay["command"] == [*ae[:-2], str(destination.parent / "replay"), ae[-1]]
            and replay["exit_code"] == 0
            and replay["input_sha256"] == sha(root / DIRECTORY / "arithmetic.llbc")
            and replay["log_sha256"] == sha(root / DIRECTORY / "replay.log")
            and replay["outputs"] == {name: sha(root / RAW / name) for name in
                                       ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")},
            "root leaf checked replay differs")
    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    targets = translated["target_information"]
    require(llbc["has_errors"] is False and translated["options"]["start_from"] == [SELECTOR]
            and translated["options"]["opaque"] == OPAQUE and len(targets) == 1
            and targets[0]["key"] == setup.TARGET and targets[0]["value"]["target_pointer_size"] == 8,
            "root leaf LLBC closure or target differs")
    expected_source = setup.SOURCE_SHA256[SOURCE]
    require(sha(root.parents[1] / SOURCE) == expected_source, "root leaf source differs")
    found = {}
    for fn in translated["fun_decls"]:
        if not fn:
            continue
        meta = fn["item_meta"]
        span = meta["span"]["Untagged"]["data"]
        source = translated["files"][span["file_id"]]
        name = meta["name"][-1].get("Ident", [""])[0]
        if source["name"] != {"Local": SOURCE} or name not in {"leaf", "charge", "advance"}:
            continue
        require(name not in found and hashlib.sha256(source["contents"].encode()).hexdigest() == expected_source,
                "root leaf embedded source differs")
        found[name] = (fn["body"], (span["beg"]["line"], span["end"]["line"]))
    require(set(found) == {"leaf", "charge", "advance"}
            and "Structured" in found["leaf"][0] and found["leaf"][1] == (347, 383)
            and found["charge"] == ("Opaque", (70, 72))
            and found["advance"] == ("Opaque", (110, 127)),
            "root leaf selected body or opaque call differs")
    types = declarations(root / RAW / "Types.lean")
    require(set(types) == {name for names in SHARED_TYPES.values() for name in names},
            "root leaf type set differs")
    for path, names in SHARED_TYPES.items():
        existing = declarations(root / "bridge" / path)
        require(all(types[name] == existing.get(name) for name in names), "root leaf shared type differs: " + path)
    bound_path = "bridge/Arithmetic/ClosedLeafGenerated.lean"
    bound = declarations(root / bound_path)
    require(receipt["verified_call_bindings"] == {name: {
        "file": bound_path, "theorem": theorem, "sha256": hashlib.sha256(bound[name].encode()).hexdigest(),
    } for name, theorem in BINDINGS.items()}, "root leaf verified application binding differs")
    declaration = declarations(root / RAW / "Funs.lean")[DECLARATION]
    require((root / ACTIVE).read_text() == HEADER + declaration + "\n\nend bulksketch\n",
            "compiled root leaf projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": 1,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + DECLARATION], "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
