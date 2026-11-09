#!/usr/bin/env python3
"""Bind the original stock checked request permission extraction to its compiled declarations."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/request-permission")
ACTIVE = Path("bridge/Arithmetic/RequestPermissionGenerated.lean")
SOURCES = ("src/sketch/input.rs", "src/sketch/state.rs")
SOURCE_COMMIT = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
CHARON_COMMIT = "7b462d9159db2ed3015162352183906a30bfafc6"
AENEAS_COMMIT = "ab34bd28458a08c150b7cbf1873e59af74588138"
ACTIVE_SHA = "c7cab7b51a1e205aca3e8d7bd1975f7b5c52f9735fea4a7e6666adeef90831ac"
LLBC_SHA = "2c0ec144ebe54f68b56f277acd973d218d747823e3d5174ec6e4c372381c29a5"
RAW_SHA = "c252587cc3f06e4a23f277f5173ed2d665c0abc99d26db77c7d9587b0aa0ced1"
INPUT = "bulksketch::sketch::input"
STATE = "bulksketch::sketch::state"
SELECTORS = [
    STATE + "::_::shape",
    f"{{impl {INPUT}::RequestInput for bulksketch::sketch::api::DecodeRequest}}::permits_id",
    f"{{impl {INPUT}::RequestInput for {INPUT}::DecodeRowsRequest}}::permits_id",
]
OPAQUE = ["bulksketch::sketch::shape::_::permits_id", INPUT + "::RequestInput"]
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest"]
FROZEN = "/-- [bulksketch::sketch::state::{bulksketch::sketch::state::FrozenSketch<F>}::shape]:"
MARKER = "/-- [bulksketch::sketch::input::{impl bulksketch::sketch::input::RequestInput<F> for bulksketch::sketch::api::DecodeRequest<"
FROZEN_PROJECTION = Path("bridge/Arithmetic/FrozenShapeGenerated.lean")
PATCH_SHA = "5efdb51e5a14db2e98c1519f9d1159e191b43df2ea1377c7e3c7528ac94f7a3e"
LIFTED = ["core::ops::deref::Deref", "core::slice::index::SliceIndex"]
TRANSFORMS = [
    "treat_box_as_builtin", "ops_to_function_calls", "index_to_function_calls",
    "reconstruct_fallible_operations", "reconstruct_panic_calls", "reconstruct_asserts",
    "reconstruct_matches", "hide_marker_traits", "hide_allocator", "remove_unused_self_clauses",
    "remove_adt_clauses", "unbind_item_vars", "deallocate_all_locals", "no_gen_tuple_structs",
]
DECLARATIONS = [
    "sketch.api.DecodeRequest.Insts.BulksketchSketchInputRequestInput.permits_id",
    "sketch.input.DecodeRowsRequest.Insts.BulksketchSketchInputRequestInput.permits_id",
]
FILES = {"Types.lean", "TypesExternal_Template.lean", "FunsExternal_Template.lean", "Funs.lean"}
ROW_LOCAL = Path("bridge/Arithmetic/RowLocalGenerated.lean")
TYPE_MODULES = {
    "Arithmetic/ReconstructionTypes": ("core.marker.PhantomData",),
    "Arithmetic/Types": ("types.FieldId", "field.sealed.Sealed", "field.BinaryField"),
    "Workmeter/Types": ("types.WorkUnits",),
    "Arithmetic/CandidateCompactGenerated": ("sketch.shape.SketchShape",),
    "Arithmetic/RowLocalGenerated": ("sketch.state.State", "sketch.state.FrozenSketch", "sketch.input.DecodeRow"),
}
ACTIVE_TYPES = (
    "sketch.api.DecodeLimits", "sketch.wire.SketchView", "sketch.plan.DecodePlan",
    "sketch.api.DecodeRequest", "sketch.input.DecodeRowsRequest",
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def type_declaration(path, name):
    match = re.search(
        r"(?m)^((?:@\[[^\n]+\]\n)*(?:def|structure|inductive) "
        + re.escape(name) + r"(?= |\n)[^\n]*(?: where| :=)[\s\S]*?)(?=\n\n)",
        path.read_text(),
    )
    require(match is not None, f"Missing declaration {name} in {path}")
    return match[1]


def check(root=ROOT, source_root=None, dependencies=None):
    source_root = source_root or root.parents[1]
    dependencies = dependencies or root
    directory = root / DIRECTORY
    receipt = json.loads((directory / "receipt.json").read_text())
    require(receipt["source_commit"] == SOURCE_COMMIT
            and receipt["charon_commit"] == CHARON_COMMIT
            and receipt["aeneas_commit"] == AENEAS_COMMIT
            and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["target"] == "x86_64-apple-darwin"
            and receipt["native_source_edited"] is False
            and receipt["native_llbc_edited"] is False,
            "Invalid stock request permission receipt")
    for relative, expected in receipt["artifacts"].items():
        require(sha(root / relative) == expected, f"Captured request permission artifact differs: {relative}")
    llbc_path = directory / "arithmetic.llbc"
    require(sha(llbc_path) == LLBC_SHA, "Original request permission LLBC differs")
    capture = json.loads(llbc_path.read_bytes())
    crate = capture["translated"]
    options = crate["options"]
    require(capture["has_errors"] is False and options["skip_borrowck"] is False
            and options["start_from"] == options["include"] == SELECTORS
            and options["opaque"] == OPAQUE and options["preset"] is None
            and options["monomorphize"] is False and options["lift_associated_types"] == LIFTED
            and all(options[option] is True for option in TRANSFORMS),
            "Request permission capture scope differs")
    require(sha(directory / "checked-selective-lift.patch") == receipt["compiler_patch_sha256"] == PATCH_SHA,
            "Scoped checked compiler patch differs")
    source_digests = {}
    for name in SOURCES:
        source = source_root / name
        files = [item for item in crate["files"] if item and item["name"] == {"Local": name}]
        require(len(files) == 1 and files[0]["contents"].encode() == source.read_bytes(),
                f"Frozen request source differs: {name}")
        source_digests[name] = sha(source)
    require(receipt["source_sha256"] == source_digests, "Request source receipt differs")
    ch, ae, replay = receipt["commands"]["charon"], receipt["commands"]["aeneas"], receipt["replay"]
    control_codes = {name: row["exit_code"] for name, row in receipt["controls"].items()}
    require(control_codes == {"checked": 0, "replay": 0, "no-check": 1, "wrong-scope": 1, "stock": 1}
            and (directory / "scoped-status").read_text().splitlines() ==
                [f"{name} exit {control_codes[name]}" for name in ("checked", "replay", "no-check", "wrong-scope")],
            "Checked translator controls differ")
    charon_argv = ch["command"]
    require(ch["exit_code"] == ae["exit_code"] == replay["exit_code"] == 0
            and charon_argv[1] == "cargo" and "--sysroot=default" in charon_argv
            and all(f"--{option.replace('_', '-')}" in charon_argv for option in TRANSFORMS)
            and all(f"--lift-associated-types={name}" in charon_argv for name in LIFTED)
            and [arg for arg in charon_argv if arg.startswith("--start-from=")]
                == [f"--start-from={name}" for name in SELECTORS]
            and [arg for arg in charon_argv if arg.startswith("--include=")]
                == [f"--include={name}" for name in SELECTORS]
            and [arg for arg in charon_argv if arg.startswith("--opaque=")]
                == [f"--opaque={name}" for name in OPAQUE]
            and charon_argv[-7:] == ["-p", "bulksketch", "--lib", "--locked", "--offline",
                                    "--target", "x86_64-apple-darwin"]
            and ae["command"][1:-2] == replay["command"][1:-2] == FLAGS
            and next(arg.removeprefix("--dest-file=") for arg in charon_argv if arg.startswith("--dest-file="))
                == ae["command"][-1] == replay["command"][-1],
            "Checked request permission commands differ")
    generated = directory / "Arithmetic"
    output_sha = {path.name: sha(path) for path in generated.glob("*.lean")}
    require(set(output_sha) == FILES and replay["output_sha256"] == output_sha,
            "Stock request permission replay differs")
    for module, names in TYPE_MODULES.items():
        for name in names:
            require(type_declaration(generated / "Types.lean", name)
                    == type_declaration(dependencies / f"bridge/{module}.lean", name),
                    f"Request permission declaration {name} differs")
    raw_path = generated / "Funs.lean"
    active_path = root / ACTIVE
    require(sha(raw_path) == RAW_SHA and sha(active_path) == ACTIVE_SHA,
            "Compiled request permission projection differs")
    raw_text, active_text = raw_path.read_text(), active_path.read_text()
    require(raw_text.count(MARKER) == active_text.count(MARKER) == 1
            and active_text[active_text.index(MARKER):] == raw_text[raw_text.index(MARKER):],
            "Checked permits_id declaration differs")
    frozen_path = dependencies / FROZEN_PROJECTION
    if not frozen_path.is_file():
        frozen_path = root.parent / "frozen-promotion" / FROZEN_PROJECTION
    frozen = frozen_path.read_text()
    require(frozen[frozen.index(FROZEN):].removesuffix("end bulksketch\n").strip()
            == raw_text[raw_text.index(FROZEN):raw_text.index(MARKER)].strip(),
            "Original captured frozen accessor differs from its standalone projection")
    for name in ACTIVE_TYPES:
        require(type_declaration(generated / "Types.lean", name) == type_declaration(active_path, name),
                f"Active request record {name} differs")
    require('local notation "alloc.sync.Arc" => Id' in (dependencies / ROW_LOCAL).read_text(),
            "Existing Arc value boundary differs")
    compiled = active_text[active_text.index(MARKER):]
    names = re.findall(r"(?m)^def\s+(sketch\.[^\s]+)", compiled)
    require(names == DECLARATIONS, "Request permission declaration inventory differs")
    return {"raw_generated_file": str(DIRECTORY / "Arithmetic/Funs.lean"),
            "raw_file_sha256": RAW_SHA, "compiled_projection": str(ACTIVE),
            "projection_file_sha256": ACTIVE_SHA, "source_declarations_retained_verbatim": len(names),
            "translator_variant": "checked-request-selective-lift-v1",
            "shared_types_and_function_dictionary_declarations_checked": True,
            "shared_arc_value_model": str(ROW_LOCAL), "reused_frozen_projection": str(FROZEN_PROJECTION),
            "generated_declarations": ["bulksketch." + name for name in names],
            "native_source_edited": False, "native_llbc_edited": False,
            "shared_types_checked": sum(map(len, TYPE_MODULES.values())),
            "active_types_checked": len(ACTIVE_TYPES)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root", type=Path)
    parser.add_argument("--dependencies", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(source_root=args.source_root, dependencies=args.dependencies), indent=2))
