#!/usr/bin/env python3
"""Verify the stock original AVX insertion-table lookup and physical layout."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SQUARE = importlib.util.spec_from_file_location("avx_square", ROOT / "extraction/avx-square/project.py")
square = importlib.util.module_from_spec(SQUARE)
SQUARE.loader.exec_module(square)
require, sha = square.require, square.sha

DIRECTORY = Path("extraction/avx-single-bases")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/AvxSingleBasesGenerated.lean")
SOURCE = "src/backend/x86_vpclmul512.rs"
BASE = "bulksketch::backend::x86_vpclmul512::"
SELECTOR = BASE + "single_bases"
OPAQUE = [BASE + "load", BASE + "INSERT_BASES"]
NAMES = ("backend.x86_vpclmul512.InsertionBases", "backend.x86_vpclmul512.single_bases")
OUTPUTS = ("Funs.lean", "FunsExternal_Template.lean", "Types.lean", "TypesExternal_Template.lean")
ARTIFACTS = {str(RAW / name) for name in OUTPUTS} | {
    str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log", "replay.log")
}
HEADER = """-- Exact stock original insertion-table type and single_bases declaration.
import Arithmetic.AvxSquareRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

"""
BINDINGS = """variable (tableModel : Result backend.x86_vpclmul512.InsertionBases)
variable (loadModel : AvxSquareRuntime.Load)

local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "backend.x86_vpclmul512.INSERT_BASES" => tableModel
local notation "backend.x86_vpclmul512.load" => loadModel

"""


def projection(root=ROOT):
    types = (root / RAW / "Types.lean").read_text()
    funs = (root / RAW / "Funs.lean").read_text()
    marker = "/-- [" + BASE + "InsertionBases]"
    fmarker = "/-- [" + BASE + "single_bases]:"
    return HEADER + types[types.index(marker):types.rindex("end bulksketch")] + BINDINGS + funs[funs.index(fmarker):]


def source_entry(crate, meta, digest):
    span = meta["span"]["Untagged"]["data"]
    source = crate["files"][span["file_id"]]
    require(source["name"] == {"Local": SOURCE} and
            hashlib.sha256(source["contents"].encode()).hexdigest() == digest,
            "AVX single-bases embedded source differs")
    return (span["beg"]["line"], span["end"]["line"])


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-square/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in ("source_commit", "rust_toolchain", "target",
                "charon_commit", "aeneas_commit", "tool_binary_sha256", "native_source_edited"))
            and receipt["selector"] == SELECTOR and receipt["opaque_application_bodies"] == OPAQUE
            and receipt["source_sha256"] == {SOURCE: parent["source_sha256"][SOURCE]}
            and set(receipt["artifacts"]) == ARTIFACTS, "invalid AVX single-bases receipt")
    for path, digest in receipt["artifacts"].items():
        require(sha(root / path) == digest, "AVX single-bases artifact differs: " + path)
    source_digest = receipt["source_sha256"][SOURCE]
    require(sha(root.parents[1] / SOURCE) == source_digest, "AVX single-bases frozen Rust source differs")
    prior = parent["commands"]["charon"]["command"]
    manifest = next(arg for arg in prior if arg.startswith("--manifest-path="))
    folder = Path(manifest.removeprefix("--manifest-path=")).parent.parent / "bulksketch-proof-evidence-20261109-avx-encode18/bases"
    capture = str(folder / "arithmetic.llbc")
    commands = receipt["commands"]
    require(set(commands) == {"charon", "aeneas", "replay"}
            and all(value["exit_code"] == 0 for value in commands.values()), "AVX single-bases capture failed")
    require(commands["charon"]["command"] == [*prior[:4], "--dest-file=" + capture, "--start-from=" + SELECTOR,
                *("--opaque=" + name for name in OPAQUE),
                "--", manifest, "-p", "bulksketch", "--lib", "--locked", "--offline", "--target", square.TARGET],
            "AVX single-bases capture command differs")
    for name, output in (("aeneas", "stock"), ("replay", "replay")):
        require(commands[name]["command"] == [parent["commands"]["aeneas"]["command"][0], *square.FLAGS,
                                              str(folder / output), capture],
                "AVX single-bases checked command differs")
    require(receipt["replayed_outputs"] == {name: sha(root / RAW / name) for name in OUTPUTS},
            "AVX single-bases replay output differs")
    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = llbc["translated"]
    opts, targets = crate["options"], crate["target_information"]
    require(llbc["has_errors"] is False and opts["start_from"] == [SELECTOR] and opts["opaque"] == OPAQUE
            and opts["dest_file"] == capture and opts["skip_borrowck"] is False and len(targets) == 1
            and targets[0]["key"] == square.TARGET and targets[0]["value"]["target_pointer_size"] == 8
            and targets[0]["value"]["is_little_endian"] is True, "AVX single-bases original LLBC scope differs")
    found = {}
    for fn in crate["fun_decls"]:
        if not fn:
            continue
        meta = fn["item_meta"]
        name = meta["name"][-1].get("Ident", [""])[0]
        if name not in ("single_bases", "load"):
            continue
        require(name not in found, "duplicate AVX single-bases original declaration")
        body = fn["body"]
        found[name] = (*source_entry(crate, meta, source_digest), body if isinstance(body, str) else next(iter(body)))
    require(found == {"single_bases": (522, 539, "Structured"), "load": (196, 200, "Opaque")},
            "AVX single-bases original body or load slot differs")
    globals_ = [g for g in crate["global_decls"] if g and g["item_meta"]["name"][-1].get("Ident", [""])[0] == "INSERT_BASES"]
    require(len(globals_) == 1 and source_entry(crate, globals_[0]["item_meta"], source_digest) == (519, 519)
            and globals_[0]["item_meta"]["opacity"] == "Opaque"
            and globals_[0]["global_kind"] == {"Static": {"is_mut": False, "is_safe": True, "is_thread_local": False}},
            "AVX single-bases static slot differs")
    types = [t for t in crate["type_decls"] if t and t["item_meta"]["name"][-1].get("Ident", [""])[0] == "InsertionBases"]
    require(len(types) == 1 and source_entry(crate, types[0]["item_meta"], source_digest) == (477, 480)
            and len(types[0]["layout"]) == 1 and types[0]["layout"][0]["key"] == square.TARGET,
            "AVX single-bases table type differs")
    layout = types[0]["layout"][0]["value"]
    offsets = [field["chosen"] for field in layout["variant_layouts"][0]["field_offsets"]]
    size = layout["size"]["chosen"]["Value"][1]["Constant"]["Value"][1][0]["Integer"]["Unsigned"]
    require(offsets == [0, 36864] and size == ["Usize", "40960"] and layout["repr"]["repr_algo"] == "C"
            and layout["repr"]["align_modif"] == {"Align": 64}, "AVX single-bases captured layout differs")
    require(set(square.declarations(root / RAW / "Types.lean")) == {NAMES[0]}
            and set(square.declarations(root / RAW / "Funs.lean")) == {NAMES[1]}
            and (root / ACTIVE).read_text() == projection(root), "compiled AVX single-bases projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(NAMES),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in NAMES],
        "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
