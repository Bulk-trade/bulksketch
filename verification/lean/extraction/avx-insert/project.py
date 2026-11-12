#!/usr/bin/env python3
"""Check scoped stock AVX insertion and horizontal reduction projections."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PARENT = importlib.util.spec_from_file_location("square", ROOT / "extraction/avx-square/project.py")
square = importlib.util.module_from_spec(PARENT)
PARENT.loader.exec_module(square)
require, sha = square.require, square.sha
DIRECTORY = Path("extraction/avx-insert")
BASE = "bulksketch::backend::x86_vpclmul512::"
SOURCE = "src/backend/x86_vpclmul512.rs"
TRAIT = "{impl bulksketch::backend::contract::BulkKernels for bulksketch::backend::x86_vpclmul512::Vpclmul512}::insert_nonzero"
TRAIT_MARKER = "/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::insert_nonzero]:"
FREE_MARKER = "/-- [" + BASE + "insert]:"
CASES = {
    "insert18": (BASE + "insert_18", [BASE + key for key in ("load", "store", "single_bases")], []),
    "horizontal": (BASE + "horizontal_xor", [], []),
    "free-dispatch": (BASE + "insert", [BASE + key for key in ("insert_18", "insert_32", "insert_single", "insert_sparse", "insert_tile")], []),
}
PROJECTIONS = {
    "insert18": ("AvxInsert18Generated", "insert18", ("backend.x86_vpclmul512.insert_18",)),
    "horizontal": ("AvxHorizontalXorGenerated", "horizontal", ("backend.x86_vpclmul512.horizontal_xor",)),
    "dispatch": ("AvxInsertDispatchGenerated", "free-dispatch",
                 tuple("backend.x86_vpclmul512.insert_loop" + str(i) + suffix for i in range(4) for suffix in (".body", ""))
                 + ("backend.x86_vpclmul512.insert",
                    "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero")),
}
MARKERS = {"insert18": "/-- [" + BASE + "insert_18]:",
           "horizontal": "/-- [" + BASE + "horizontal_xor]:", "dispatch": FREE_MARKER}
OUTPUTS = {
    "insert18": ("Funs.lean", "FunsExternal_Template.lean", "Types.lean", "TypesExternal_Template.lean"),
    "horizontal": ("Funs.lean", "FunsExternal_Template.lean", "Types.lean", "TypesExternal_Template.lean"),
    "free-dispatch": ("Funs.lean", "FunsExternal_Template.lean", "Types.lean", "TypesExternal_Template.lean"),
    "trait-dispatch": ("Funs.lean", "FunsExternal_Template.lean", "Types.lean"),
}
HEADERS = {'insert18': '-- Exact original AVX insert_18 declaration from checked stock extraction.\nimport Arithmetic.AvxEncode18Generated\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.dupNamespace false\nset_option linter.unusedVariables false\n\nnamespace bulksketch\n\nvariable (baseModel : AvxEncode18Runtime.Bases)\nvariable (loadModel : AvxSquareRuntime.Load)\nvariable (storeModel : AvxSquareRuntime.Store)\n\nlocal notation "core.core_arch.x86.__m512i" => Avx512Register.Word512\nlocal notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords\nlocal notation "backend.x86_vpclmul512.powers_18" => (backend.x86_vpclmul512.powers_18 baseModel)\nlocal notation "backend.x86_vpclmul512.load" => loadModel\nlocal notation "backend.x86_vpclmul512.store" => storeModel\n\n', 'horizontal': '-- Exact original horizontal reduction from checked stock extraction.\nimport Arithmetic.AvxSquareRuntime\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\n\nnamespace Aeneas.Std.AvxHorizontalRuntime\n\nopen Avx512Register\n\nabbrev Pair128 := BitVec 64 × BitVec 64\n\ndef selectPair (mask : I32) (index : Fin 4) : Fin 4 :=\n  ⟨(mask.bv.toNat >>> (2 * index.val)) % 4, Nat.mod_lt _ (by decide)⟩\n\ndef shufflePairs (mask : I32) (left right : Word512) : Result Word512 :=\n  .ok (fun pair high => if pair.val < 2 then left (selectPair mask pair) high else right (selectPair mask pair) high)\n\n/-- The original body uses only 0x4e, swapping the 64-bit halves of each\n128-bit pair. The scope here is that immediate. -/\ndef shuffleDwords (mask : I32) (value : Word512) : Result Word512 :=\n  if mask = 78#i32 then .ok (fun pair high => value pair (!high)) else .fail .panic\n\ndef lowPair (value : Word512) : Result Pair128 := .ok (value 0 false, value 0 true)\n\ndef lowWord (value : Pair128) : Result I64 := .ok ⟨value.1⟩\n\nend Aeneas.Std.AvxHorizontalRuntime\n\nnamespace bulksketch\n\nlocal notation "core.core_arch.x86.__m512i" => Avx512Register.Word512\nlocal notation "core.core_arch.x86.avx512f._mm512_shuffle_i64x2" => AvxHorizontalRuntime.shufflePairs\nlocal notation "core.core_arch.x86.avx512f._mm512_shuffle_epi32" => AvxHorizontalRuntime.shuffleDwords\nlocal notation "core.core_arch.x86.avx512f._mm512_castsi512_si128" => AvxHorizontalRuntime.lowPair\nlocal notation "core.core_arch.x86_64.sse2._mm_cvtsi128_si64" => AvxHorizontalRuntime.lowWord\nlocal notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords\nlocal notation "core.num.I64.to_ne_bytes" => X86PclmulRuntime.signedBytes\nlocal notation "core.num.U64.from_ne_bytes" => X86PclmulRuntime.unsignedFromBytes\n\n', 'dispatch': '-- Original checked AVX free and public insertion dispatch declarations.\nimport Arithmetic.AvxHornerChunkRuntime\nimport Arithmetic.PortableInsertionGenerated\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.dupNamespace false\nset_option linter.unusedVariables false\n\nnamespace Aeneas.Std.AvxInsertDispatchRuntime\n\nabbrev Single := Slice U64 → U64 → Result (Slice U64)\nabbrev SingleCapacity := Usize → Slice U64 → U64 → Result (Slice U64)\nabbrev Batch := Slice U64 → Slice U64 → Result (Slice U64)\nabbrev Tile := Usize → Bool → Batch\n\nend Aeneas.Std.AvxInsertDispatchRuntime\n\nnamespace bulksketch\n\nvariable (insert18Model : AvxInsertDispatchRuntime.Single)\nvariable (insert32Model : AvxInsertDispatchRuntime.Single)\nvariable (singleModel : AvxInsertDispatchRuntime.SingleCapacity)\nvariable (sparseModel : AvxInsertDispatchRuntime.Batch)\nvariable (tileModel : AvxInsertDispatchRuntime.Tile)\n\nlocal notation "core.slice.iter.Chunks" => AvxHornerChunkRuntime.ChunkState\nlocal notation "core.slice.Slice.chunks" => AvxHornerChunkRuntime.chunks\nlocal notation "core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next" =>\n  AvxHornerChunkRuntime.nextShared\nlocal notation "backend.x86_vpclmul512.insert_18" => insert18Model\nlocal notation "backend.x86_vpclmul512.insert_32" => insert32Model\nlocal notation "backend.x86_vpclmul512.insert_single" => singleModel\nlocal notation "backend.x86_vpclmul512.insert_sparse" => sparseModel\nlocal notation "backend.x86_vpclmul512.insert_tile" => tileModel\n\n'}
SOURCES = {'insert18': [('insert_18', 'src/backend/x86_vpclmul512.rs', 542, 549, 'Structured'), ('powers_18', 'src/backend/x86_vpclmul512.rs', 569, 610, 'Structured'), ('load', 'src/backend/x86_vpclmul512.rs', 196, 200, 'Opaque'), ('store', 'src/backend/x86_vpclmul512.rs', 203, 206, 'Opaque'), ('single_bases', 'src/backend/x86_vpclmul512.rs', 522, 539, 'Opaque'), ('multiply', 'src/backend/x86_vpclmul512.rs', 287, 297, 'Structured'), ('raw', 'src/backend/x86_vpclmul512.rs', 209, 214, 'Structured'), ('reduce_cl', 'src/backend/x86_vpclmul512.rs', 279, 284, 'Structured'), ('reduce_shift', 'src/backend/x86_vpclmul512.rs', 261, 276, 'Structured'), ('call', 'src/backend/x86_vpclmul512.rs', 266, 274, 'Structured'), ('call_once', 'src/backend/x86_vpclmul512.rs', 266, 274, 'Structured'), ('call_mut', 'src/backend/x86_vpclmul512.rs', 266, 274, 'Structured')], 'horizontal': [('horizontal_xor', 'src/backend/x86_vpclmul512.rs', 253, 258, 'Structured')], 'free-dispatch': [('insert', 'src/backend/x86_vpclmul512.rs', 396, 425, 'Structured'), ('insert_18', 'src/backend/x86_vpclmul512.rs', 542, 549, 'Opaque'), ('insert_32', 'src/backend/x86_vpclmul512.rs', 616, 705, 'Opaque'), ('insert_single', 'src/backend/x86_vpclmul512.rs', 712, 747, 'Opaque'), ('insert_sparse', 'src/backend/x86_vpclmul512.rs', 431, 435, 'Opaque'), ('insert_tile', 'src/backend/x86_vpclmul512.rs', 438, 459, 'Opaque')], 'trait-dispatch': [('insert_nonzero', 'src/backend/x86_vpclmul512.rs', 133, 142, 'Structured'), ('square_mod', 'src/backend/x86_vpclmul512.rs', 106, 114, 'Opaque'), ('multiply_linear', 'src/backend/x86_vpclmul512.rs', 116, 122, 'Opaque'), ('odd_recurrence_matches', 'src/backend/x86_vpclmul512.rs', 124, 131, 'Opaque'), ('encode_nonzero', 'src/backend/x86_vpclmul512.rs', 144, 158, 'Opaque'), ('xor_assign', 'src/backend/x86_vpclmul512.rs', 160, 164, 'Opaque'), ('difference', 'src/backend/x86_vpclmul512.rs', 166, 178, 'Opaque'), ('horner_many', 'src/backend/x86_vpclmul512.rs', 180, 187, 'Opaque'), ('insert_nonzero', 'src/backend/portable.rs', 85, 100, 'Opaque'), ('insert', 'src/backend/x86_vpclmul512.rs', 396, 425, 'Opaque'), ('square_mod', 'src/backend/contract.rs', 53, 55, 'Structured'), ('multiply_linear', 'src/backend/contract.rs', 59, 63, 'Structured'), ('odd_recurrence_matches', 'src/backend/contract.rs', 68, 82, 'Structured'), ('encode_nonzero', 'src/backend/contract.rs', 88, 97, 'Structured'), ('difference', 'src/backend/contract.rs', 103, 118, 'Structured'), ('mul', 'src/backend/x86_vpclmul512.rs', 50, 52, 'Opaque'), ('square', 'src/backend/x86_vpclmul512.rs', 53, 55, 'Opaque'), ('frobenius', 'src/backend/x86_vpclmul512.rs', 56, 58, 'Opaque'), ('inverse', 'src/backend/x86_vpclmul512.rs', 59, 61, 'Opaque'), ('trace', 'src/backend/x86_vpclmul512.rs', 62, 64, 'Opaque'), ('solve_quadratic', 'src/backend/x86_vpclmul512.rs', 65, 67, 'Opaque'), ('raw_mul', 'src/backend/x86_vpclmul512.rs', 68, 70, 'Opaque'), ('reduce', 'src/backend/x86_vpclmul512.rs', 71, 73, 'Opaque'), ('scale_xor', 'src/backend/x86_vpclmul512.rs', 86, 93, 'Opaque'), ('square_slice', 'src/backend/x86_vpclmul512.rs', 95, 102, 'Opaque'), ('xor_assign', 'src/backend/portable.rs', 102, 107, 'Opaque'), ('horner_many', 'src/backend/portable.rs', 109, 120, 'Opaque'), ('default', 'src/types.rs', 266, 266, 'Structured'), ('mul', 'src/backend/portable.rs', 14, 16, 'Opaque'), ('square', 'src/backend/portable.rs', 18, 20, 'Opaque'), ('frobenius', 'src/backend/portable.rs', 22, 24, 'Opaque'), ('inverse', 'src/backend/portable.rs', 26, 32, 'Opaque'), ('trace', 'src/backend/portable.rs', 34, 36, 'Opaque'), ('solve_quadratic', 'src/backend/portable.rs', 38, 40, 'Opaque'), ('raw_mul', 'src/backend/portable.rs', 42, 44, 'Opaque'), ('reduce', 'src/backend/portable.rs', 46, 48, 'Opaque'), ('scale_xor', 'src/backend/portable.rs', 62, 74, 'Opaque'), ('square_slice', 'src/backend/portable.rs', 76, 81, 'Opaque'), ('clone', 'src/backend/x86_vpclmul512.rs', 27, 27, 'Structured'), ('clone', 'src/backend/portable.rs', 10, 10, 'Opaque')]}


def raw(root, label, filename="Funs.lean"):
    return root / DIRECTORY / label / "Arithmetic" / filename


def artifacts():
    return {str(DIRECTORY / label / "Arithmetic" / name) for label, files in OUTPUTS.items() for name in files} | {
        str(DIRECTORY / label / name) for label in OUTPUTS for name in ("arithmetic.llbc", "charon.log", "aeneas.log", "replay.log")
    }


def trait_case(root):
    prior = json.loads((root / "extraction/avx-horner/receipt.json").read_text())["captures"]["trait-scoped"]
    opaque = [arg.removeprefix("--opaque=") for arg in prior["charon"] if arg.startswith("--opaque=")]
    opaque = [name for name in opaque if name != BASE + "_::insert_nonzero"]
    return TRAIT, [*opaque, BASE + "_::horner_many", BASE + "insert"], [TRAIT]


def body(root, mode):
    label = PROJECTIONS[mode][1]
    source = raw(root, label).read_text()
    value = source[source.index(MARKERS[mode]):]
    if mode != "dispatch":
        return value
    value = value[:value.rindex("end bulksketch")]
    for i in range(4):
        name = f"backend.x86_vpclmul512.insert_loop{i}.body"
        marker = FREE_MARKER + f" loop {i}:"
        value = value.replace(marker, f'local notation "{name}" => ({name} tileModel)\n\n' + marker)
    dispatch_bindings = "".join(f'local notation "backend.x86_vpclmul512.insert_loop{i}" => (backend.x86_vpclmul512.insert_loop{i} tileModel)\n' for i in range(4))
    value = value.replace(FREE_MARKER + "\n", dispatch_bindings + "\n" + FREE_MARKER + "\n")
    value += ('local notation "backend.x86_vpclmul512.insert" =>\n'
              '  (backend.x86_vpclmul512.insert insert18Model insert32Model singleModel sparseModel tileModel)\n\n')
    trait = raw(root, "trait-dispatch").read_text()
    return value + trait[trait.index(TRAIT_MARKER):]


def check(root=ROOT, entry="dispatch"):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-square/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in ("source_commit", "rust_toolchain", "target",
                "charon_commit", "aeneas_commit", "tool_binary_sha256", "native_source_edited"))
            and set(receipt["captures"]) == set(OUTPUTS) and set(receipt["artifacts"]) == artifacts(),
            "invalid AVX insert receipt")
    for path, digest in receipt["artifacts"].items():
        require(sha(root / path) == digest, "AVX insert artifact differs: " + path)
    source_paths = {item[1] for entries in SOURCES.values() for item in entries}
    require(receipt["source_sha256"] == {path: sha(root.parents[1] / path) for path in source_paths}
            and receipt["source_sha256"][SOURCE] == parent["source_sha256"][SOURCE],
            "AVX insert frozen Rust source differs")
    prior_charon = parent["commands"]["charon"]["command"]
    manifest = next(arg for arg in prior_charon if arg.startswith("--manifest-path="))
    workspace = Path(manifest.removeprefix("--manifest-path=")).parent.parent
    for label, (selector, opaque, included) in {**CASES, "trait-dispatch": trait_case(root)}.items():
        cap_dir = (workspace / "bulksketch-proof-evidence-20261109-avx-encode18/insert18" if label == "insert18"
                   else workspace / "bulksketch-proof-evidence-20261109-avx-insert18" / label)
        cap_file = str(cap_dir / "arithmetic.llbc")
        capture = receipt["captures"][label]
        require(capture["capture"] == 0 and capture["translation"] == 0
                and capture["replay"]["exit_code"] == 0
                and capture["replay"]["outputs"] == {name: sha(raw(root, label, name)) for name in OUTPUTS[label]},
                "AVX insert checked replay differs: " + label)
        require(capture["charon"] == [*prior_charon[:4], "--dest-file=" + cap_file, "--start-from=" + selector,
            *("--opaque=" + name for name in opaque), *("--include=" + name for name in included),
            "--", manifest, "-p", "bulksketch", "--lib", "--locked", "--offline", "--target", square.TARGET],
            "AVX insert capture command differs: " + label)
        flags = [parent["commands"]["aeneas"]["command"][0], *square.FLAGS]
        require(capture["aeneas"] == [*flags, str(cap_dir / "stock"), cap_file]
                and capture["replay"]["command"] == [*flags, str(cap_dir / "replay"), cap_file],
                "AVX insert checked command differs: " + label)
        llbc = json.loads((root / DIRECTORY / label / "arithmetic.llbc").read_text())
        crate = llbc["translated"]
        opts, targets = crate["options"], crate["target_information"]
        require(llbc["has_errors"] is False and opts["start_from"] == [selector] and opts["include"] == included
                and opts["opaque"] == opaque and opts["dest_file"] == cap_file and opts["skip_borrowck"] is False
                and len(targets) == 1 and targets[0]["key"] == square.TARGET
                and targets[0]["value"]["target_pointer_size"] == 8, "AVX insert LLBC scope differs: " + label)
        found = []
        for fn in crate["fun_decls"]:
            if not fn:
                continue
            meta = fn["item_meta"]
            span = meta["span"]["Untagged"]["data"]
            file = crate["files"][span["file_id"]]
            path = file["name"].get("Local", "")
            if not path.startswith("src/"):
                continue
            require(path in source_paths and hashlib.sha256(file["contents"].encode()).hexdigest() == receipt["source_sha256"][path],
                    "AVX insert embedded source differs: " + label)
            value = fn["body"]
            found.append((meta["name"][-1].get("Ident", [""])[0], path, span["beg"]["line"], span["end"]["line"],
                          value if isinstance(value, str) else next(iter(value))))
        require(sorted(found) == sorted(SOURCES[label]), "AVX insert native body or slot differs: " + label)
    raw18 = raw(root, "insert18").read_text()
    raw_encode = (root / "extraction/avx-encode-18/Arithmetic/Funs.lean").read_text()
    powers = "/-- [" + BASE + "powers_18]:"
    encode = "/-- [" + BASE + "encode_18]:"
    require(raw18[raw18.index(powers):raw18.index(MARKERS["insert18"])] ==
            raw_encode[raw_encode.index(powers):raw_encode.index(encode)],
            "AVX insert_18 imported powers_18 differs")
    for mode, (module, label, names) in PROJECTIONS.items():
        active = Path("bridge/Arithmetic") / (module + ".lean")
        require((root / active).read_text() == HEADERS[mode] + body(root, mode),
                "compiled AVX insert projection differs: " + mode)
    module, label, names = PROJECTIONS[entry]
    active = Path("bridge/Arithmetic") / (module + ".lean")
    selected = DIRECTORY / label / "Arithmetic/Funs.lean"
    return {"raw_generated_file": str(selected), "raw_file_sha256": sha(root / selected),
        "compiled_projection": str(active), "projection_file_sha256": sha(root / active),
        "source_declarations_retained_verbatim": len(names), "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in names], "native_source_edited": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--entry", choices=PROJECTIONS, default="dispatch")
    args = parser.parse_args()
    print(json.dumps(check(entry=args.entry), indent=2))
