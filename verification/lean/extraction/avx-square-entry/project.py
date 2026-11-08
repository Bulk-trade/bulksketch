#!/usr/bin/env python3
"""Verify the verbatim original AVX modular-square selector."""
import hashlib
import json
from pathlib import Path
import re
import runpy

ROOT = Path(__file__).resolve().parents[2]
COMMON = runpy.run_path(str(ROOT / "extraction/avx-square/project.py"))
require, sha, declarations, compact = (COMMON[name] for name in ("require", "sha", "declarations", "compact"))
DIRECTORY = Path("extraction/avx-square-entry")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/AvxSquareEntryGenerated.lean")
SOURCE = COMMON["SOURCE"]
SCOPE = "bulksketch::backend::x86_vpclmul512"
SELECTOR = "{impl bulksketch::backend::contract::BulkKernels for bulksketch::backend::x86_vpclmul512::Vpclmul512}::square_mod"
SIBLINGS = ("mul", "square", "frobenius", "inverse", "trace", "solve_quadratic", "raw_mul", "reduce",
            "scale_xor", "square_slice", "multiply_linear", "odd_recurrence_matches", "insert_nonzero",
            "encode_nonzero", "xor_assign", "difference", "horner_many")
OPAQUE = [*(SCOPE + "::_::" + method for method in SIBLINGS), SCOPE + "::square_mod",
          "bulksketch::backend::portable::_::_", "bulksketch::backend::x86_pclmul::_::_"]
NAME = "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.square_mod"
ARTIFACTS = {
    *(str(RAW / name) for name in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")),
    *(str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log", "replay.log")),
}
HEADER = """-- Exact original AVX modular-square selector with its proved free callee.
import Arithmetic.AvxSquareGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

variable (loadModel : Aeneas.Std.AvxSquareRuntime.Load)
variable (storeModel : Aeneas.Std.AvxSquareRuntime.Store)

local notation "backend.x86_vpclmul512.square_mod" =>
  (backend.x86_vpclmul512.square_mod loadModel storeModel)

"""

def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    prior = json.loads((root / "extraction/avx-square/receipt.json").read_text())
    require(all(receipt[key] == prior[key] for key in
                ("source_commit", "rust_toolchain", "target", "charon_commit", "aeneas_commit",
                 "tool_binary_sha256", "source_sha256", "native_source_edited"))
            and set(receipt["artifacts"]) == ARTIFACTS,
            "AVX square selector receipt differs")
    for artifact, digest in receipt["artifacts"].items():
        require(sha(root / artifact) == digest, "AVX square selector artifact differs: " + artifact)
    require(sha(root.parents[1] / SOURCE) == receipt["source_sha256"][SOURCE], "AVX square selector source differs")
    controls = receipt["commands"]
    require(set(controls) == {"charon", "aeneas", "replay"} and
            all(row["exit_code"] == 0 for row in controls.values()), "AVX square selector replay outcome differs")
    parent_capture = prior["commands"]["charon"]["command"]
    manifest = next(word for word in parent_capture if word.startswith("--manifest-path="))
    capture_dir = Path(manifest.removeprefix("--manifest-path=")).parent.parent / (
        "bulksketch-proof-evidence-20261109-avx-square/entry-siblings")
    capture_file = capture_dir / "arithmetic.llbc"
    require(controls["charon"]["command"] == [
        *parent_capture[:4], "--dest-file=" + str(capture_file), "--start-from=" + SELECTOR,
        *["--opaque=" + name for name in OPAQUE], "--include=" + SELECTOR,
        "--", manifest, "-p", "bulksketch", "--lib", "--locked", "--offline", "--target", COMMON["TARGET"],
    ], "AVX square selector capture command differs")
    aeneas = prior["commands"]["aeneas"]["command"][0]
    for name, out in (("aeneas", "stock"), ("replay", "replay")):
        require(controls[name]["command"] == [aeneas, *COMMON["FLAGS"], str(capture_dir / out), str(capture_file)],
                "AVX square selector checked command differs")
    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = llbc["translated"]
    opts = crate["options"]
    require(llbc["has_errors"] is False and opts["start_from"] == [SELECTOR] and
            opts["opaque"] == OPAQUE and opts["include"] == [SELECTOR] and
            opts["dest_file"] == str(capture_file) and
            len(crate["target_information"]) == 1 and crate["target_information"][0]["key"] == COMMON["TARGET"],
            "AVX square selector LLBC scope differs")
    entries = {}
    for fn in crate["fun_decls"]:
        if not fn:
            continue
        meta = fn["item_meta"]
        if meta["name"][:3] != [{"Ident": [part, 0]} for part in ("bulksketch", "backend", "x86_vpclmul512")]:
            continue
        if meta["name"][-1].get("Ident") != ["square_mod", 0]:
            continue
        span = meta["span"]["Untagged"]["data"]
        file = crate["files"][span["file_id"]]
        require(file["name"] == {"Local": SOURCE} and
                hashlib.sha256(file["contents"].encode()).hexdigest() == receipt["source_sha256"][SOURCE],
                "AVX square selector embedded source differs")
        entries[span["beg"]["line"]] = (span["end"]["line"],
            isinstance(fn["body"], dict) and "Structured" in fn["body"])
    require(entries == {106: (114, True), 218: (250, False)},
            "AVX square selector body or original free callee slot differs")
    raw = (root / RAW / "Funs.lean").read_text()
    start = raw.index("/-- [bulksketch::backend::x86_vpclmul512::{impl")
    body = raw[start:raw.rindex("end bulksketch")].strip()
    require((root / ACTIVE).read_text() == HEADER + body + "\n\nend bulksketch\n",
            "compiled AVX square selector projection differs")
    require(re.findall(r"(?m)^def\s+(backend\.x86_vpclmul512\.\S+)", body) == [NAME],
            "AVX square selector declaration set changed")
    shared = declarations(root / "bridge/Arithmetic/Types.lean")
    raw_types = declarations(root / RAW / "Types.lean")
    for name in ("types.RawProduct", "field.BinaryField"):
        require(compact(raw_types[name]) == compact(shared[name]),
                "AVX square selector shared type differs: " + name)
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": 1,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + NAME],
        "native_source_edited": False,
    }

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
