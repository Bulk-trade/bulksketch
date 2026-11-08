#!/usr/bin/env python3
"""Verify the original monic-GCD wrapper and its explicit div/rem slot."""
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
COMMON = importlib.util.spec_from_file_location("root_setup", ROOT / "extraction/root-setup/project.py")
shared = importlib.util.module_from_spec(COMMON)
COMMON.loader.exec_module(shared)
require, sha, declarations = shared.require, shared.sha, shared.declarations

DIRECTORY = Path("extraction/dense-monic-gcd")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/DenseGcdGenerated.lean")
MODULE = "bulksketch::poly::dense"
DIVISION = "poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into"
FUNCTION = "poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into"
SOURCE = "src/poly/dense.rs"
SOURCE_SHA256 = "13b360fba6387dda36a9655f3f67d01be6752e4ca6b7f8e1824e7333bf3da644"
ARTIFACTS = {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "replay.log",
    "Arithmetic/Funs.lean", "Arithmetic/FunsExternal_Template.lean", "Arithmetic/Types.lean",
)}
HEADER = """-- Exact original Dense monic GCD and both loop declarations.
import Arithmetic.DenseExactDivideGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace Aeneas.Std.DenseGcdRuntime

/-- Both mutable slots are swapped in the forward direction, and the
returned pair is swapped back to the caller's original slot order. -/
def swapSlots {T : Type} (left right : T) : T × T × (T × T → T × T) :=
  (right, left, Prod.swap)

end Aeneas.Std.DenseGcdRuntime

namespace bulksketch

variable (division : DenseDivisionRuntime.DivRem)
local notation "poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into" => division
local notation "core.mem.swap" => DenseGcdRuntime.swapSlots
"""


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["source_commit"] == shared.SOURCE and receipt["target"] == shared.TARGET
            and receipt["aeneas_commit"] == shared.AENEAS and receipt["charon_commit"] == shared.CHARON
            and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["native_source_edited"] is False and receipt["binary_sha256"] == shared.BINARY_SHA256
            and set(receipt["files_sha256"]) == ARTIFACTS, "invalid monic GCD receipt")
    for path, expected in receipt["files_sha256"].items():
        require(sha(root / path) == expected, "monic GCD artifact differs: " + path)
    commands = receipt["commands"]
    require([(entry["name"], entry["exit_code"]) for entry in commands] == [("charon", 0), ("aeneas", 0)],
            "monic GCD capture outcome differs")
    ch, ae = (entry["command"] for entry in commands)
    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    source_root = Path(manifest.removeprefix("--manifest-path=")).parent
    evidence = source_root.parent / "bulksketch-proof-evidence-20261109-dense-reducer/monic_gcd_into-isolated"
    input_path = str(evidence / "arithmetic.llbc")
    flags = ["-backend", "lean", "-sequential", "-no-progress-bar", "-print-error-emitters",
             "-split-files", "-checks", "-dest"]
    require(ch == [parent["charon_command"][0], "cargo", "--preset=aeneas", "--sysroot=default",
                   "--dest-file=" + input_path, "--start-from=" + MODULE, "--opaque=" + MODULE + "::_::_",
                   "--include=" + MODULE + "::_::monic_gcd_into", "--opaque=" + MODULE + "::normalized_len",
                   "--", manifest, "-p", "bulksketch", "--lib", "--locked", "--target", shared.TARGET]
            and ae == [str(source_root / "verification/lean/tooling/aeneas/src/_build/default/main.exe"),
                       *flags, str(evidence / "stock"), input_path],
            "monic GCD checked extraction command differs")
    replay = receipt["replay"]
    require(replay["command"] == [*ae[:-2],
                str(source_root.parent / "bulksketch-proof-evidence-20261109-dense-division/monic-gcd-replay"),
                input_path] and replay["exit_code"] == 0
            and replay["outputs"] == {name: sha(root / RAW / name)
                                       for name in ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")},
            "monic GCD checked replay differs")

    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    options = translated["options"]
    targets = translated["target_information"]
    require(llbc["has_errors"] is False and options["start_from"] == [MODULE]
            and options["include"] == [MODULE + "::_::monic_gcd_into"]
            and options["opaque"] == [MODULE + "::_::_", MODULE + "::normalized_len"]
            and options["dest_file"] == input_path and len(targets) == 1
            and targets[0]["key"] == shared.TARGET and targets[0]["value"]["target_pointer_size"] == 8,
            "monic GCD LLBC scope differs")
    found = {}
    for fn in translated["fun_decls"]:
        if not fn:
            continue
        meta = fn["item_meta"]
        name = meta["name"][-1].get("Ident", [None])[0]
        if name not in ("div_rem_into", "monic_gcd_into", "swap"):
            continue
        span = meta["span"]["Untagged"]["data"]
        source = translated["files"][span["file_id"]]
        if name == "swap":
            require(source["name"] == {"Local": "/rustc/library/core/src/mem/mod.rs"},
                    "monic GCD scoped swap is not the Rust core intrinsic")
        else:
            require(source["name"] == {"Local": SOURCE}
                    and source["contents"].encode() == (root.parents[1] / SOURCE).read_bytes()
                    and sha(root.parents[1] / SOURCE) == SOURCE_SHA256,
                    "monic GCD original source differs")
        require(name not in found, "monic GCD duplicate captured definition: " + name)
        body = fn["body"]
        found[name] = (span["beg"], span["end"], body if isinstance(body, str) else next(iter(body)))
    require(found == {
        "div_rem_into": ({"line": 40, "col": 4}, {"line": 96, "col": 5}, "Opaque"),
        "monic_gcd_into": ({"line": 113, "col": 4}, {"line": 153, "col": 5}, "Structured"),
        "swap": ({"line": 830, "col": 0}, {"line": 830, "col": 42}, "Opaque"),
    }, "monic GCD wrapper or div/rem slot differs")

    types = declarations(root / RAW / "Types.lean")
    references = {
        "bridge/Arithmetic/Types.lean": {"types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"},
        "bridge/Arithmetic/SliceKernelTypes.lean": {"backend.contract.Arithmetic", "backend.contract.BulkKernels"},
    }
    for path, names in references.items():
        current = declarations(root / path)
        require(all(types[name] == current.get(name) for name in names), "monic GCD shared type differs: " + path)
    external = (root / RAW / "FunsExternal_Template.lean").read_text()
    require("""axiom poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice
    types.RawProduct → Result ((Std.Usize × Std.Usize) × (Slice Std.U64) ×
    (Slice Std.U64) × (Slice types.RawProduct))""" in external,
        "monic GCD callee signature differs")
    exact_parent = (root / "bridge/Arithmetic/DenseExactDivideGenerated.lean").read_text()
    require("""abbrev DivRem := ∀ {F K : Type}, bulksketch.field.BinaryField F →
    bulksketch.backend.contract.BulkKernels K F →
    Slice U64 → Slice U64 → Slice U64 → Slice U64 → Slice bulksketch.types.RawProduct →
    Result ((Usize × Usize) × Slice U64 × Slice U64 × Slice bulksketch.types.RawProduct)""" in exact_parent,
            "monic GCD imported div/rem slot differs")
    funcs = declarations(root / RAW / "Funs.lean")
    loop = FUNCTION + "_loop"
    active = HEADER + "\n" + funcs[loop + ".body"] + "\n\n"
    active += f'local notation "{loop}.body" => ({loop}.body division)\n\n'
    active += funcs[loop] + "\n\n"
    active += f'local notation "{loop}" => ({loop} division)\n\n'
    active += funcs[FUNCTION] + "\n\nend bulksketch\n"
    require((root / ACTIVE).read_text() == active, "compiled monic GCD projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": 3,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in (loop + ".body", loop, FUNCTION)], "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
