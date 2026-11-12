#!/usr/bin/env python3
"""Verify the stock modular shift body and its scoped overlapping-copy binding."""
import importlib.util
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
COMMON = importlib.util.spec_from_file_location("root_setup", ROOT / "extraction/root-setup/project.py")
shared = importlib.util.module_from_spec(COMMON)
COMMON.loader.exec_module(shared)
require, sha, declarations = shared.require, shared.sha, shared.declarations

EXTRACTION = Path("extraction/times-x-mod")
RAW = EXTRACTION / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/TimesXModGenerated.lean")
RUNTIME = Path("bridge/Arithmetic/TimesXModRuntime.lean")
RUNTIME_SHA256 = "ab56ac64657578ba81e6d128d07bbfeb837d71af394e72c03f5f59d2293a3868"
SOURCE = "src/poly/dense.rs"
SOURCE_SHA256 = "13b360fba6387dda36a9655f3f67d01be6752e4ca6b7f8e1824e7333bf3da644"
SELECTOR = "bulksketch::poly::dense::times_x_mod"
FUNCTION = "poly.dense.times_x_mod"
DICTIONARY = "core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds"
ARTIFACTS = {str(EXTRACTION / name) for name in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "replay.log",
    "Arithmetic/Funs.lean", "Arithmetic/FunsExternal_Template.lean", "Arithmetic/Types.lean",
)}
HEADER = """-- Original checked Dense modular shift and RangeTo dictionary.
import Arithmetic.TimesXModRuntime

open Aeneas Aeneas.Std Result Error
set_option linter.unusedVariables false

namespace bulksketch

"""


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    require(receipt["source_commit"] == shared.SOURCE and receipt["selector"] == SELECTOR
            and receipt["target"] == shared.TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["aeneas_commit"] == shared.AENEAS and receipt["charon_commit"] == shared.CHARON
            and receipt["binary_sha256"] == shared.BINARY_SHA256 and receipt["native_source_edited"] is False
            and receipt["checked_exit"] == 0 and set(receipt["files_sha256"]) == ARTIFACTS,
            "invalid modular shift receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "modular shift artifact differs: " + path)
    ch, ae, replay = receipt["charon_command"], receipt["aeneas_command"], receipt["replay"]
    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    require(ch[0] == parent["charon_command"][0] and ae[0] == parent["aeneas_command"][0]
            and ch[1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"]
            and ch[4] == "--dest-file=" + ae[-1]
            and ch[5:] == ["--start-from=" + SELECTOR, "--", manifest,
                           "-p", "bulksketch", "--lib", "--locked", "--target", shared.TARGET]
            and ae[1:-2] == shared.FLAGS and Path(ae[-1]).parts[-2:] == ("times-x-mod", "arithmetic.llbc")
            and Path(ae[-2]) == Path(ae[-1]).parent / "stock"
            and replay["command"][:-2] == ae[:-2] and replay["command"][-1] == ae[-1]
            and Path(replay["command"][-2]).name == "times-x-replay"
            and replay["exit_code"] == 0 and replay["outputs"] == {name: sha(root / RAW / name)
                for name in ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")},
            "modular shift checked capture or replay differs")

    llbc = json.loads((root / EXTRACTION / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    options = translated["options"]
    targets = translated["target_information"]
    require(llbc["has_errors"] is False and options["start_from"] == [SELECTOR]
            and options["opaque"] == [] and options["dest_file"] == ae[-1]
            and len(targets) == 1 and targets[0]["key"] == shared.TARGET
            and targets[0]["value"]["target_pointer_size"] == 8, "modular shift LLBC scope differs")
    source_functions = {}
    for f in translated["fun_decls"]:
        if f:
            meta = f["item_meta"]
            name = meta["name"][-1].get("Ident", [None])[0]
            if name in ("times_x_mod", "copy_within"):
                require(name not in source_functions, "duplicate modular shift input")
                span = meta["span"]["Untagged"]["data"]
                source = translated["files"][span["file_id"]]
                source_functions[name] = f["body"], span, source
    body, span, source = source_functions["times_x_mod"]
    require("Structured" in body and span["beg"] == {"line": 234, "col": 0}
            and span["end"] == {"line": 240, "col": 1} and source["name"] == {"Local": SOURCE}
            and source["contents"].encode() == (root.parents[1] / SOURCE).read_bytes()
            and sha(root.parents[1] / SOURCE) == SOURCE_SHA256, "original modular shift source differs")
    body, span, source = source_functions["copy_within"]
    require(body == "Opaque" and span["beg"] == {"line": 4376, "col": 4}
            and source["name"] == {"Local": "/rustc/library/core/src/slice/mod.rs"},
            "scoped copy_within binding changed")

    types = declarations(root / RAW / "Types.lean")
    shared_types = {
        "bridge/Arithmetic/Types.lean": {"types.RawProduct", "types.FieldId",
                                         "field.sealed.Sealed", "field.BinaryField"},
        "bridge/Arithmetic/SliceKernelTypes.lean": {"backend.contract.Arithmetic", "backend.contract.BulkKernels"},
    }
    copied_types = {"core.ops.range.Bound", "core.ops.range.RangeBounds"}
    require(set(types) == copied_types | set().union(*shared_types.values()), "modular shift type set changed")
    for path, names in shared_types.items():
        current = declarations(root / path)
        require(all(types[name] == current.get(name) for name in names), "modular shift shared type differs: " + path)
    runtime = (root / RUNTIME).read_text()
    require(sha(root / RUNTIME) == RUNTIME_SHA256 and all(types[name] in runtime for name in copied_types),
            "modular shift runtime binding differs")
    externals = set(re.findall(r"(?m)^axiom\s+(\S+)", (root / RAW / "FunsExternal_Template.lean").read_text()))
    require(externals == {DICTIONARY + ".start_bound", DICTIONARY + ".end_bound",
                          "core.slice.Slice.copy_within", "core.slice.raw.from_ref"},
            "modular shift external declaration set changed")
    functions = declarations(root / RAW / "Funs.lean")
    expected = HEADER + "\n\n".join(functions[name] for name in (DICTIONARY, FUNCTION)) + "\n\nend bulksketch\n"
    require((root / ACTIVE).read_text() == expected, "compiled modular shift projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": 4,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in (DICTIONARY, FUNCTION, *sorted(copied_types))],
        "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
