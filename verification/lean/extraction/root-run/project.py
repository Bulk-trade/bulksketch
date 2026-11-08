#!/usr/bin/env python3
"""Check the exact stock Roots::run projection and source-backed callees."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
COMMON = importlib.util.spec_from_file_location("root_setup", ROOT / "extraction/root-setup/project.py")
shared = importlib.util.module_from_spec(COMMON)
COMMON.loader.exec_module(shared)
require, sha, declarations = shared.require, shared.sha, shared.declarations

DIRECTORY = Path("extraction/root-run")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/RootRunGenerated.lean")
HEADER_SHA256 = "90e400bb2da5ac4e829e0f9c505a2903285aaa750368d0823b20862e6e636fc7"
SELECTOR = "bulksketch::decode::roots::_::run"
ROOTS = "src/decode/roots.rs"
AFFINE = "src/decode/affine.rs"
DENSE = "src/poly/dense.rs"
SCOPES = ["bulksketch::decode::roots::_::" + name for name in
          ("closed_leaf", "leaf", "prepare_affine", "enumerate_affine", "trace", "divide")]
SCOPES += ["bulksketch::decode::affine::splitter",
           "bulksketch::poly::dense::_::prepare_square_table",
           "bulksketch::poly::dense::_::monic_gcd_into"]
SPANS = {
    "run": (ROOTS, 128, 4, 236, 5, "Structured"),
    "closed_leaf": (ROOTS, 237, 4, 272, 5, "Opaque"),
    "leaf": (ROOTS, 347, 4, 383, 5, "Opaque"),
    "prepare_affine": (ROOTS, 274, 4, 319, 5, "Opaque"),
    "enumerate_affine": (ROOTS, 321, 4, 345, 5, "Opaque"),
    "trace": (ROOTS, 384, 4, 443, 5, "Opaque"),
    "divide": (ROOTS, 444, 4, 490, 5, "Opaque"),
    "subspace_start": (AFFINE, 245, 0, 247, 1, "Structured"),
    "splitter": (AFFINE, 270, 0, 297, 1, "Opaque"),
    "prepare_square_table": (DENSE, 167, 4, 186, 5, "Opaque"),
    "monic_gcd_into": (DENSE, 113, 4, 153, 5, "Opaque"),
}
NAMES = ("decode.affine.subspace_start", "decode.roots.Roots.run")
ARTIFACTS = {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "replay.log",
    "Arithmetic/Funs.lean", "Arithmetic/FunsExternal_Template.lean", "Arithmetic/Types.lean",
)}
SHARED_TYPES = {
    "Types": {"types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"},
    "SliceKernelTypes": {"backend.contract.Arithmetic", "backend.contract.BulkKernels"},
    "ReconstructionTypes": {"decode.roots.Roots", "decode.scratch.SplitterBasis", "decode.scratch.FactorFrame",
                            "decode.scratch.RowWorkspace", "types.Stage", "types.DecodeFailure"},
    "RootSetupGenerated": {"decode.roots.FactorWork"},
    "WorkScheduleGenerated": {"decode.work.Charge"},
}
REUSED = {
    "RootSetupGenerated": {"decode.roots.FactorWork.new"},
    "ClosedLeafGenerated": {"decode.roots.charge", "types.Stage.Insts.CoreCmpPartialEqStage.eq"},
}


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["source_commit"] == shared.SOURCE and receipt["target"] == shared.TARGET
            and receipt["aeneas_commit"] == shared.AENEAS and receipt["charon_commit"] == shared.CHARON
            and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["native_source_edited"] is False and receipt["binary_sha256"] == shared.BINARY_SHA256
            and receipt["checked_exit"] == 0 and set(receipt["files_sha256"]) == ARTIFACTS,
            "invalid root run receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "root run artifact differs: " + path)
    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    work = Path(manifest.removeprefix("--manifest-path=")).parent.parent
    capture = work / "bulksketch-proof-evidence-20261109-root-traversal/run"
    input_file = str(capture / "arithmetic.llbc")
    ch, ae = receipt["charon_command"], receipt["aeneas_command"]
    require(ch == [parent["charon_command"][0], "cargo", "--preset=aeneas", "--sysroot=default",
                   "--dest-file=" + input_file, "--start-from=" + SELECTOR,
                   *("--opaque=" + name for name in SCOPES), "--", manifest,
                   "-p", "bulksketch", "--lib", "--locked", "--target", shared.TARGET]
            and ae == [parent["aeneas_command"][0], *shared.FLAGS, str(capture / "stock"), input_file],
            "root run checked capture command differs")
    replay = receipt["replay"]
    require(replay["command"] == [*ae[:-2], str(work / "bulksketch-proof-evidence-20261109-native-root-run/replay"),
                                  input_file] and replay["exit_code"] == 0
            and replay["outputs"] == {name: sha(root / RAW / name)
                                       for name in ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")},
            "root run checked replay differs")

    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = llbc["translated"]
    opts = crate["options"]
    targets = crate["target_information"]
    require(llbc["has_errors"] is False and opts["start_from"] == [SELECTOR] and opts["opaque"] == SCOPES
            and opts["dest_file"] == input_file and len(targets) == 1 and targets[0]["key"] == shared.TARGET
            and targets[0]["value"]["target_pointer_size"] == 8, "root run LLBC scope differs")
    found = {}
    for f in crate["fun_decls"]:
        if not f:
            continue
        meta = f["item_meta"]
        name = meta["name"][-1].get("Ident", [None])[0]
        if name not in SPANS:
            continue
        span = meta["span"]["Untagged"]["data"]
        file = crate["files"][span["file_id"]]
        path = SPANS[name][0]
        require(file["name"] == {"Local": path} and name not in found
                and file["contents"].encode() == (root.parents[1] / path).read_bytes(),
                "root run original source differs: " + name)
        body = f["body"]
        found[name] = (path, span["beg"]["line"], span["beg"]["col"], span["end"]["line"], span["end"]["col"],
                       body if isinstance(body, str) else next(iter(body)))
    require(found == SPANS, "root run original body or callee slot differs")
    types = declarations(root / RAW / "Types.lean")
    funcs = declarations(root / RAW / "Funs.lean")
    for groups, original in ((SHARED_TYPES, types), (REUSED, funcs)):
        for path, names in groups.items():
            current = declarations(root / "bridge/Arithmetic" / (path + ".lean"))
            require(all(original[name] == current.get(name) for name in names),
                    "root run shared source declaration differs: " + path)
    active = (root / ACTIVE).read_text()
    header, marker, body = active.partition("/-- [bulksketch::decode::affine::subspace_start]:")
    require(hashlib.sha256(header.encode()).hexdigest() == HEADER_SHA256
            and marker + body == "\n\n".join(funcs[name] for name in NAMES) + "\n\nend bulksketch\n",
            "compiled root run projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": 2,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in NAMES],
        "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
