#!/usr/bin/env python3
"""Verify the original accelerated modular-square projection."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/avx-square")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/AvxSquareGenerated.lean")
RUNTIME = Path("bridge/Arithmetic/AvxSquareRuntime.lean")
SOURCE = "src/backend/x86_vpclmul512.rs"
SCALAR_SOURCE = "src/backend/x86_pclmul.rs"
SELECTOR = "bulksketch::backend::x86_vpclmul512::square_mod"
NAME = "backend.x86_vpclmul512.square_mod"
TOOLCHAIN = "nightly-2026-09-17"
TARGET = "x86_64-apple-darwin"
FLAGS = ("-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest")
NAMES = tuple(NAME + suffix for suffix in (
    "_loop0.body", "_loop0", "_loop1_loop0.body", "_loop1_loop0",
    "_loop1.body", "_loop1", "",
))
ARTIFACTS = {
    *(str(RAW / name) for name in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")),
    *(str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log", "replay.log")),
}
HEADER = """-- Exact original AVX square kernel. The masked memory operations are explicit slots.
import Arithmetic.AvxSquareRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace bulksketch

variable (loadModel : Aeneas.Std.AvxSquareRuntime.Load)
variable (storeModel : Aeneas.Std.AvxSquareRuntime.Store)

local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "core.core_arch.x86.avx512f._mm512_setzero_si512" => AvxSquareRuntime.zero
local notation "core.core_arch.x86.avx512f._mm512_set1_epi64" => Avx512Register.broadcast
local notation "core.core_arch.x86.avx512f._mm512_unpacklo_epi64" => Avx512Register.unpack false
local notation "core.core_arch.x86.avx512f._mm512_unpackhi_epi64" => Avx512Register.unpack true
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "core.num.Usize.div_ceil" => DenseReducerSquareRuntime.divCeil
local notation "core.num.U64.to_ne_bytes" => X86PclmulRuntime.unsignedBytes
local notation "core.num.I64.from_ne_bytes" => X86PclmulRuntime.signedFromBytes
local notation "core.iter.adapters.skip.Skip" => AvxSquareRuntime.Skip
local notation "core.iter.traits.iterator.Iterator.skip.default" => AvxSquareRuntime.skip
local notation "core.iter.adapters.skip.Skip.Insts.CoreIterTraitsIteratorIterator.next" => AvxSquareRuntime.skipNext
local notation "backend.x86_vpclmul512.load" => loadModel
local notation "backend.x86_vpclmul512.store" => storeModel

"""

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def declarations(path):
    result = {}
    for block in re.split(r"(?m)(?=^/--)", path.read_text()):
        declaration = re.search(r"(?m)^(?:def|abbrev|structure|inductive|axiom)\s+(\S+)", block)
        if declaration:
            result[declaration.group(1)] = block.removesuffix("end bulksketch\n").strip()
    return result

def compact(block):
    return re.sub(r"\s+", "", block[block.index("-/") + 2:])

def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/dense-reducer-square/receipt.json").read_text())
    require(receipt["source_commit"] == parent["source_commit"] and
            receipt["charon_commit"] == parent["charon_commit"] and
            receipt["aeneas_commit"] == parent["aeneas_commit"] and
            receipt["rust_toolchain"] == TOOLCHAIN and receipt["target"] == TARGET and
            receipt["native_source_edited"] is False and
            receipt["tool_binary_sha256"] == parent["base_binary_sha256"] and
            set(receipt["artifacts"]) == ARTIFACTS, "invalid accelerated square receipt")
    for artifact, digest in receipt["artifacts"].items():
        require(sha(root / artifact) == digest, "AVX square artifact differs: " + artifact)
    require(sha(root / RUNTIME) == receipt["runtime_sha256"], "AVX square runtime binding differs")
    require(receipt["source_sha256"] == {name: sha(root.parents[1] / name)
                                       for name in (SOURCE, SCALAR_SOURCE)}, "AVX square native source differs")
    controls = receipt["commands"]
    require(set(controls) == {"charon", "aeneas", "replay"} and
            all(row["exit_code"] == 0 for row in controls.values()), "AVX square replay outcome differs")
    capture = controls["charon"]["command"]
    prior = parent["charon_command"]
    manifest = next(word for word in prior if word.startswith("--manifest-path="))
    capture_root = Path(manifest.removeprefix("--manifest-path=")).parent
    capture_dir = capture_root.parent / "bulksketch-proof-evidence-20261109-avx-square/free-only"
    capture_file = capture_dir / "arithmetic.llbc"
    opaque = ["bulksketch::backend::x86_vpclmul512::" + name for name in ("load", "store")]
    require(capture == [*prior[:4], "--dest-file=" + str(capture_file), "--start-from=" + SELECTOR,
                        *["--opaque=" + name for name in opaque],
                        "--", manifest, "-p", "bulksketch", "--lib", "--locked", "--offline",
                        "--target", TARGET], "AVX square capture command differs")
    aeneas = parent["commands"]["stock"]["command"][0]
    for name, out in (("aeneas", "stock"), ("replay", "replay")):
        require(controls[name]["command"] == [aeneas, *FLAGS, str(capture_dir / out), str(capture_file)],
                "AVX square checked command differs")
    data = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = data["translated"]
    opts = crate["options"]
    require(data["has_errors"] is False and opts["start_from"] == [SELECTOR] and
            opts["opaque"] == opaque and opts["dest_file"] == str(capture_file) and
            len(crate["target_information"]) == 1 and crate["target_information"][0]["key"] == TARGET,
            "AVX square original LLBC scope differs")
    found = {}
    expected = {"square_mod": (218, 250, True), "load": (196, 200, False), "store": (203, 206, False)}
    for f in crate["fun_decls"]:
        if not f:
            continue
        meta = f["item_meta"]
        if meta["name"][:3] != [{"Ident": [part, 0]} for part in ("bulksketch", "backend", "x86_vpclmul512")]:
            continue
        name = meta["name"][-1].get("Ident", [None])[0]
        if name not in expected:
            continue
        span = meta["span"]["Untagged"]["data"]
        file = crate["files"][span["file_id"]]
        require(file["name"] == {"Local": SOURCE} and
                hashlib.sha256(file["contents"].encode()).hexdigest() == receipt["source_sha256"][SOURCE],
                "AVX square embedded source differs")
        found[name] = (span["beg"]["line"], span["end"]["line"],
                       isinstance(f["body"], dict) and "Structured" in f["body"])
    require(found == expected, "AVX square source spans or memory slots differ")

    raw = (root / RAW / "Funs.lean").read_text()
    start = raw.index("/-- [bulksketch::backend::x86_vpclmul512::square_mod]: loop body 0:")
    body = raw[start:raw.rindex("end bulksketch")].strip()
    for marker, prior_name, args in (("loop 2:", "square_mod_loop1_loop0.body", "loadModel"),
                                     ("loop body 1:", "square_mod_loop1_loop0", "loadModel"),
                                     ("loop 1:", "square_mod_loop1.body", "loadModel storeModel")):
        target = "/-- [bulksketch::backend::x86_vpclmul512::square_mod]: " + marker
        name = "backend.x86_vpclmul512." + prior_name
        body = body.replace(target, f'local notation "{name}" =>\n  ({name} {args})\n\n' + target)
    target = "/-- [bulksketch::backend::x86_vpclmul512::square_mod]:\n"
    body = body.replace(target, 'local notation "backend.x86_vpclmul512.square_mod_loop1" =>\n'
                        '  (backend.x86_vpclmul512.square_mod_loop1 loadModel storeModel)\n\n' + target)
    require((root / ACTIVE).read_text() == HEADER + body + "\n\nend bulksketch\n",
            "compiled AVX square projection differs")

    original = declarations(root / RAW / "Funs.lean")
    for path, names in {
        "bridge/Arithmetic/Avx512RegisterGenerated.lean": ("backend.x86_vpclmul512.raw", "backend.x86_vpclmul512.reduce_shift"),
        "bridge/Arithmetic/X86PclmulGenerated.lean": ("backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.square",),
        "bridge/Arithmetic/Funs.lean": ("field.Gf64.Insts.BulksketchFieldBinaryField",),
    }.items():
        current = declarations(root / path)
        for name in names:
            require(compact(current[name]) == compact(original[name]), "AVX square shared declaration differs: " + name)
    require(tuple(re.findall(r"(?m)^def (backend\.x86_vpclmul512\.square_mod\S*)", body)) == NAMES,
            "AVX square declaration set changed")
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
