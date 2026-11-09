#!/usr/bin/env python3
"""Verify the checked original AVX Horner kernel and both stock dispatch bodies."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
SQUARE = importlib.util.spec_from_file_location("avx_square", ROOT / "extraction/avx-square/project.py")
square = importlib.util.module_from_spec(SQUARE)
SQUARE.loader.exec_module(square)
require, sha = square.require, square.sha

DIRECTORY = Path("extraction/avx-horner")
ACTIVE = Path("bridge/Arithmetic/AvxHornerGenerated.lean")
RUNTIME = Path("bridge/Arithmetic/AvxHornerChunkRuntime.lean")
SOURCE = "src/backend/x86_vpclmul512.rs"
PORTABLE = "src/backend/portable.rs"
BASE = "bulksketch::backend::x86_vpclmul512::"
TRAIT = "{impl bulksketch::backend::contract::BulkKernels for bulksketch::backend::x86_vpclmul512::Vpclmul512}::horner_many"
VARIANT = "checked-ended-shared-scalar-v1"
SELECTORS = {"kernel": BASE + "horner_kernel", "free-selector": BASE + "horner_many", "trait-scoped": TRAIT}
KERNEL_MARKER = "/-- [bulksketch::backend::x86_vpclmul512::horner_kernel]:"
FREE_MARKER = "/-- [bulksketch::backend::x86_vpclmul512::horner_many]:"
TRAIT_MARKER = ("/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> "
                "for bulksketch::backend::x86_vpclmul512::Vpclmul512}::horner_many]:")
NAMES = tuple("backend.x86_vpclmul512.horner_kernel" + suffix for suffix in
              ("_loop0_loop0.body", "_loop0_loop0", "_loop0.body", "_loop0", "")) + (
    "backend.x86_vpclmul512.horner_many",
    "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.horner_many",
)
OUTPUTS = ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")
EXPECT = {
    "kernel": {(SOURCE, "horner_kernel", 377, 393, "Structured"),
               (SOURCE, "load", 196, 200, "Opaque"), (SOURCE, "store", 203, 206, "Opaque")},
    "free-selector": {(SOURCE, "horner_many", 372, 374, "Structured"),
                      (SOURCE, "horner_kernel", 377, 393, "Opaque")},
    "trait-scoped": {(SOURCE, "horner_many", 180, 187, "Structured"),
                     (SOURCE, "horner_many", 372, 374, "Opaque"),
                     (PORTABLE, "horner_many", 109, 120, "Opaque")},
}
NATIVE_NAMES = {"horner_kernel", "horner_many", "load", "store"}
CLOSURE = "backend.x86_vpclmul512.reduce_shift.closure"
REVERSE = "core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT"
CHUNKS = {
    "core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice",
    "core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice",
}
HEADER = """-- Exact declarations from the reviewed checked kernel and stock selector captures.
import Arithmetic.AvxHornerChunkRuntime
import Arithmetic.PortableHornerGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

variable (loadModel : Aeneas.Std.AvxSquareRuntime.Load)
variable (storeModel : Aeneas.Std.AvxSquareRuntime.Store)

local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "core.core_arch.x86.avx512f._mm512_set1_epi64" => Avx512Register.broadcast
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "core.num.U64.to_ne_bytes" => X86PclmulRuntime.unsignedBytes
local notation "core.num.I64.from_ne_bytes" => X86PclmulRuntime.signedFromBytes
local notation "core.slice.Slice.split_last" => PortableHornerRuntime.splitLast
local notation "backend.x86_vpclmul512.load" => loadModel
local notation "backend.x86_vpclmul512.store" => storeModel
local notation "core.slice.iter.Chunks" => AvxHornerChunkRuntime.ChunkState
local notation "core.slice.iter.ChunksMut" => AvxHornerChunkRuntime.ChunkState
local notation "core.slice.Slice.chunks" => AvxHornerChunkRuntime.chunks
local notation "core.slice.Slice.chunks_mut" => AvxHornerChunkRuntime.chunksMut
local notation "core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice" =>
  (fun T => @AvxHornerChunkRuntime.nextShared T)
local notation "core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice" =>
  (fun T => @AvxHornerChunkRuntime.nextMutable T)
local notation "core.iter.traits.collect.IntoIterator.Blanket" => AvxHornerChunkRuntime.chunkBlanket
local notation "core.iter.traits.iterator.Iterator.zip.trait_default" => AvxHornerChunkRuntime.zipConstruct
local notation "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next" =>
  AvxHornerChunkRuntime.zipNext

"""


def declarations(path):
    result = {}
    for block in re.split(r"(?m)(?=^/--)", path.read_text()):
        declaration = re.search(r"(?m)^(?:def|impl_def|abbrev|structure|inductive|axiom)\s+(\S+)", block)
        if declaration:
            name = declaration.group(1)
            require(name not in result, "duplicate AVX Horner declaration: " + name)
            result[name] = block.removesuffix("end bulksketch\n").strip()
    return result


def artifacts(label):
    names = OUTPUTS + (("TypesExternal_Template.lean",) if label == "kernel" else ())
    return {str(DIRECTORY / label / "Arithmetic" / name) for name in names} | {
        str(DIRECTORY / label / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log", "replay.log")
    }


def selected(raw, marker):
    return raw[raw.index(marker):raw.rindex("end bulksketch")]


def projection(root=ROOT):
    pieces = [
        selected((root / DIRECTORY / label / "Arithmetic/Funs.lean").read_text(), marker)
        for label, marker in (("kernel", KERNEL_MARKER), ("free-selector", FREE_MARKER), ("trait-scoped", TRAIT_MARKER))
    ]
    body = "".join(pieces)
    for marker, suffix in ((KERNEL_MARKER + " loop 0:", "horner_kernel_loop0.body"),
                           (KERNEL_MARKER + "\n", "horner_kernel_loop0"),
                           (FREE_MARKER, "horner_kernel"), (TRAIT_MARKER, "horner_many")):
        name = "backend.x86_vpclmul512." + suffix
        body = body.replace(marker, f'local notation "{name}" => ({name} loadModel storeModel)\n\n' + marker)
    return HEADER + body + "end bulksketch\n"


def expected_opaque(root):
    prior = json.loads((root / "extraction/avx-square-entry/receipt.json").read_text())
    args = prior["commands"]["charon"]["command"]
    sibling = [arg.removeprefix("--opaque=") for arg in args if arg.startswith("--opaque=")]
    sibling[sibling.index(BASE + "_::horner_many")] = BASE + "_::square_mod"
    sibling.insert(sibling.index(BASE + "square_mod"), BASE + "horner_many")
    return {"kernel": [BASE + "load", BASE + "store"], "free-selector": [BASE + "horner_kernel"],
            "trait-scoped": sibling}


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-square/receipt.json").read_text())
    variant = json.loads((root / "tooling/aeneas-horner-match/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in ("source_commit", "target", "rust_toolchain",
            "aeneas_commit", "charon_commit", "tool_binary_sha256", "native_source_edited"))
            and receipt["translator_variant"] == VARIANT
            and receipt["variant_binary_sha256"] == variant["patched_binary_sha256"]
            and receipt["variant_patch_sha256"] == sha(root / "tooling/aeneas-horner-match/ended-shared-scalar.patch")
            and set(receipt["captures"]) == set(SELECTORS)
            and set(receipt["source_sha256"]) == {SOURCE, PORTABLE}
            and receipt["source_sha256"][SOURCE] == parent["source_sha256"][SOURCE]
            and receipt["runtime_sha256"] == sha(root / RUNTIME), "invalid AVX Horner receipt")
    require(receipt["source_sha256"] == {path: sha(root.parents[1] / path) for path in (SOURCE, PORTABLE)},
            "AVX Horner Rust source differs")
    prior = parent["commands"]["charon"]["command"]
    manifest = next(arg for arg in prior if arg.startswith("--manifest-path="))
    base = Path(manifest.removeprefix("--manifest-path=")).parent.parent / "bulksketch-proof-evidence-20261109-avx-horner"
    opaque = expected_opaque(root)
    require(set(receipt["artifacts"]) == set().union(*(artifacts(label) for label in SELECTORS)) | {
        str(DIRECTORY / name) for name in ("stock-kernel-rejection.log", "unchecked-kernel-rejection.log", "rust-std.sha256")
    }, "AVX Horner artifact set differs")
    for path, digest in receipt["artifacts"].items():
        require(sha(root / path) == digest, "AVX Horner artifact differs: " + path)
    for label, selector in SELECTORS.items():
        data = receipt["captures"][label]
        folder = base / label
        llbc_path = root / DIRECTORY / label / "arithmetic.llbc"
        expected_llbc = str(folder / "arithmetic.llbc")
        included = [selector] if label == "trait-scoped" else []
        use_variant = label == "kernel"
        expected_binary = variant["patched_binary_sha256"] if use_variant else variant["baseline_binary_sha256"]
        names = OUTPUTS + (("TypesExternal_Template.lean",) if use_variant else ())
        require(data["capture"] == 0 and data["checked_exit"] == 0 and data["replay"]["exit_code"] == 0
                and data["replay"]["input_sha256"] == sha(llbc_path)
                and data["replay"]["binary_sha256"] == expected_binary
                and data["replay"]["outputs"] == {
                    name: sha(root / DIRECTORY / label / "Arithmetic" / name) for name in names},
                "AVX Horner checked replay differs: " + label)
        require(data["charon"] == [*prior[:4], "--dest-file=" + expected_llbc, "--start-from=" + selector,
                *("--opaque=" + value for value in opaque[label]), *("--include=" + value for value in included),
                "--", manifest, "-p", "bulksketch", "--lib", "--locked", "--offline", "--target", square.TARGET],
                "AVX Horner Charon command differs: " + label)
        command = data["checked_command"]
        binary = receipt["kernel_variant_command_binary"] if use_variant else parent["commands"]["aeneas"]["command"][0]
        output = "ended-scalar" if use_variant else "stock"
        require(command == [binary, *square.FLAGS, str(folder / output), expected_llbc]
                and data["replay"]["command"] == [binary, *square.FLAGS, str(folder / "replay"), expected_llbc],
                "AVX Horner checked command differs: " + label)
        llbc = json.loads(llbc_path.read_text())
        crate = llbc["translated"]
        opts, targets = crate["options"], crate["target_information"]
        require(llbc["has_errors"] is False and opts["start_from"] == [selector] and opts["include"] == included
                and opts["opaque"] == opaque[label] and opts["dest_file"] == expected_llbc
                and opts["skip_borrowck"] is False and len(targets) == 1
                and targets[0]["key"] == square.TARGET and targets[0]["value"]["target_pointer_size"] == 8,
                "AVX Horner LLBC closure differs: " + label)
        found = set()
        for fn in crate["fun_decls"]:
            if not fn:
                continue
            meta = fn["item_meta"]
            name = meta["name"][-1].get("Ident", [""])[0]
            span = meta["span"]["Untagged"]["data"]
            source = crate["files"][span["file_id"]]
            path = source["name"].get("Local", "")
            if name not in NATIVE_NAMES or not path.startswith("src/"):
                continue
            body = fn["body"]
            kind = body if isinstance(body, str) else next(iter(body))
            entry = (path, name, span["beg"]["line"], span["end"]["line"], kind)
            require(entry not in found and path in receipt["source_sha256"]
                    and hashlib.sha256(source["contents"].encode()).hexdigest() == receipt["source_sha256"][path],
                    "AVX Horner embedded source differs: " + label)
            found.add(entry)
        require(found == EXPECT[label], "AVX Horner native selector or opaque boundary differs: " + label)
    controls = receipt["kernel_controls"]
    require(set(controls) == {"stock", "unchecked"} and all(row["exit_code"] == 1 for row in controls.values()),
            "AVX Horner baseline controls changed")
    require(controls["stock"]["command"] == [parent["commands"]["aeneas"]["command"][0], *square.FLAGS,
                str(base / "kernel/stock"), str(base / "kernel/arithmetic.llbc")]
            and controls["unchecked"]["command"] == [receipt["kernel_variant_command_binary"],
                *(flag for flag in square.FLAGS if flag != "-checks"), str(base / "kernel/without-checks"),
                str(base / "kernel/arithmetic.llbc")],
            "AVX Horner baseline commands changed")
    for log in ("stock-kernel-rejection.log", "unchecked-kernel-rejection.log"):
        data = (root / DIRECTORY / log).read_text()
        require("Could not match the contexts" in data and "InterpJoin.ml, line 1571" in data,
                "AVX Horner baseline failure changed: " + log)

    raw = DIRECTORY / "kernel/Arithmetic/Funs.lean"
    original = declarations(root / raw)
    registers = declarations(root / "bridge/Arithmetic/Avx512RegisterGenerated.lean")
    shared = {name for name in registers if name.startswith("backend.x86_vpclmul512.")} - {CLOSURE}
    require(set(original) == shared | {REVERSE} | CHUNKS | set(NAMES[:5]), "AVX Horner kernel declarations differ")
    require(all(original[name] == registers[name] for name in shared),
            "AVX Horner imported register declaration differs")
    reverse = declarations(root / "bridge/Arithmetic/DenseNormalizationGenerated.lean")[REVERSE]
    require(original[REVERSE] == reverse, "AVX Horner imported reverse iterator differs")
    require(declarations(root / DIRECTORY / "kernel/Arithmetic/Types.lean") == {CLOSURE: registers[CLOSURE]},
            "AVX Horner closure type differs")
    require((root / ACTIVE).read_text() == projection(root), "compiled AVX Horner projection differs")
    return {
        "raw_generated_file": str(raw), "raw_file_sha256": sha(root / raw),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(NAMES),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in NAMES],
        "native_source_edited": False, "translator_variant": VARIANT,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
