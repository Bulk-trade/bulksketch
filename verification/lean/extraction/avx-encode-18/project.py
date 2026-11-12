#!/usr/bin/env python3
"""Verify the original AVX capacity-18 encoder projection."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SQUARE = importlib.util.spec_from_file_location("avx_square", ROOT / "extraction/avx-square/project.py")
square = importlib.util.module_from_spec(SQUARE)
SQUARE.loader.exec_module(square)
require, sha, declarations = square.require, square.sha, square.declarations

DIRECTORY = Path("extraction/avx-encode-18")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/AvxEncode18Generated.lean")
REGISTERS = Path("bridge/Arithmetic/Avx512RegisterGenerated.lean")
RUNTIME = Path("bridge/Arithmetic/AvxEncode18Runtime.lean")
SOURCE = "src/backend/x86_vpclmul512.rs"
SELECTOR = "bulksketch::backend::x86_vpclmul512::encode_18"
OPAQUE = ["bulksketch::backend::x86_vpclmul512::" + name for name in ("store", "single_bases")]
NAMES = ("backend.x86_vpclmul512.powers_18", "backend.x86_vpclmul512.encode_18")
OUTPUTS = ("Funs.lean", "FunsExternal_Template.lean", "Types.lean", "TypesExternal_Template.lean")
ARTIFACTS = {str(RAW / name) for name in OUTPUTS} | {
    str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log", "replay.log")
}
EXPECTED = {
    "encode_18": (552, 565, "Structured"), "powers_18": (569, 610, "Structured"),
    "single_bases": (522, 539, "Opaque"),
    "store": (203, 206, "Opaque"), "multiply": (287, 297, "Structured"),
    "raw": (209, 214, "Structured"), "reduce_cl": (279, 284, "Structured"),
    "reduce_shift": (261, 276, "Structured"), "call": (266, 274, "Structured"),
    "call_once": (266, 274, "Structured"), "call_mut": (266, 274, "Structured"),
}
CLOSURE = "backend.x86_vpclmul512.reduce_shift.closure"
HEADER = """-- Exact declarations from checked stock captures.
import Arithmetic.AvxEncode18Runtime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

variable (baseModel : AvxEncode18Runtime.Bases)
variable (storeModel : AvxSquareRuntime.Store)

local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "core.core_arch.x86.avx512f._mm512_set1_epi64" => Avx512Register.broadcast
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "core.core_arch.x86.avx512f._mm512_set_epi64" => AvxEncode18Runtime.set8
local notation "core.core_arch.x86.avx512f._mm512_permutexvar_epi64" => AvxEncode18Runtime.permute
local notation "core.core_arch.x86.avx512f._mm512_permutex2var_epi64" => AvxEncode18Runtime.permuteTwo
local notation "core.core_arch.x86.avx512f._mm512_mask_mov_epi64" => AvxEncode18Runtime.maskMove
local notation "core.num.U64.to_ne_bytes" => X86PclmulRuntime.unsignedBytes
local notation "core.num.I64.from_ne_bytes" => X86PclmulRuntime.signedFromBytes
local notation "backend.x86_vpclmul512.single_bases" => baseModel
local notation "backend.x86_vpclmul512.store" => storeModel

"""


def projection(root=ROOT):
    original = declarations(root / RAW / "Funs.lean")
    parts = []
    for index, name in enumerate(NAMES):
        if index:
            prior = NAMES[index - 1]
            parts.append(f'local notation "{prior}" => ({prior} baseModel)')
        parts.append(original[name])
    return HEADER + "\n\n".join(parts) + "\n\nend bulksketch\n"


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-square/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in (
                "source_commit", "rust_toolchain", "target", "charon_commit", "aeneas_commit",
                "tool_binary_sha256", "native_source_edited"))
            and receipt["selector"] == SELECTOR and receipt["opaque_application_bodies"] == OPAQUE
            and receipt["source_sha256"] == {SOURCE: parent["source_sha256"][SOURCE]}
            and set(receipt["artifacts"]) == ARTIFACTS, "invalid AVX capacity-18 encoder receipt")
    for path, digest in receipt["artifacts"].items():
        require(sha(root / path) == digest, "AVX capacity-18 encoder artifact differs: " + path)
    require(sha(root / RUNTIME) == receipt["runtime_sha256"], "AVX capacity-18 encoder runtime differs")
    source_digest = receipt["source_sha256"][SOURCE]
    require(sha(root.parents[1] / SOURCE) == source_digest, "AVX capacity-18 encoder Rust source differs")

    commands = receipt["commands"]
    require(set(commands) == {"charon", "aeneas", "replay"}
            and all(row["exit_code"] == 0 for row in commands.values()), "AVX capacity-18 encoder replay failed")
    prior = parent["commands"]["charon"]["command"]
    manifest = next(word for word in prior if word.startswith("--manifest-path="))
    capture_dir = Path(manifest.removeprefix("--manifest-path=")).parent.parent / (
        "bulksketch-proof-evidence-20261109-avx-encode18/encode18")
    capture_file = capture_dir / "arithmetic.llbc"
    require(commands["charon"]["command"] == [
        *prior[:4], "--dest-file=" + str(capture_file), "--start-from=" + SELECTOR,
        *("--opaque=" + name for name in OPAQUE),
        "--", manifest, "-p", "bulksketch", "--lib", "--locked", "--offline", "--target", square.TARGET,
    ], "AVX capacity-18 encoder capture command differs")
    for name, output in (("aeneas", "stock"), ("replay", "replay")):
        require(commands[name]["command"] == [parent["commands"]["aeneas"]["command"][0], *square.FLAGS,
                                              str(capture_dir / output), str(capture_file)],
                "AVX capacity-18 encoder checked command differs")
    require(receipt["replayed_outputs"] == {name: sha(root / RAW / name) for name in OUTPUTS},
            "AVX capacity-18 encoder checked outputs differ")

    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    opts, targets = translated["options"], translated["target_information"]
    require(llbc["has_errors"] is False and opts["start_from"] == [SELECTOR]
            and opts["opaque"] == OPAQUE and opts["dest_file"] == str(capture_file)
            and opts["skip_borrowck"] is False and len(targets) == 1
            and targets[0]["key"] == square.TARGET and targets[0]["value"]["target_pointer_size"] == 8,
            "AVX capacity-18 encoder original LLBC scope differs")
    found = {}
    for fn in translated["fun_decls"]:
        if not fn:
            continue
        meta = fn["item_meta"]
        span = meta["span"]["Untagged"]["data"]
        source = translated["files"][span["file_id"]]
        file = source["name"].get("Local", "")
        if not file.startswith("src/"):
            continue
        name = meta["name"][-1].get("Ident", [""])[0]
        require(file == SOURCE and name not in found
                and hashlib.sha256(source["contents"].encode()).hexdigest() == source_digest,
                "AVX capacity-18 encoder embedded source differs")
        body = fn["body"]
        found[name] = (span["beg"]["line"], span["end"]["line"], body if isinstance(body, str) else next(iter(body)))
    require(found == EXPECTED, "AVX capacity-18 encoder original closure differs")

    original = declarations(root / RAW / "Funs.lean")
    current = declarations(root / REGISTERS)
    expected_registers = {name for name in current if name.startswith("backend.x86_vpclmul512.")} - {CLOSURE}
    require(set(original) == set(NAMES) | expected_registers, "AVX capacity-18 encoder declaration set differs")
    require(all(original[name] == current[name] for name in expected_registers),
            "AVX capacity-18 encoder imported register declaration differs")
    require(declarations(root / RAW / "Types.lean") == {CLOSURE: current[CLOSURE]},
            "AVX capacity-18 encoder imported closure type differs")
    require((root / ACTIVE).read_text() == projection(root), "compiled AVX capacity-18 encoder projection differs")
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
