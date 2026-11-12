#!/usr/bin/env python3
"""Verify the scoped original canonicalization and checked slice-pattern variant."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIR = Path("extraction/canonicalize")
ACTIVE = Path("bridge/Arithmetic/CanonicalizeGenerated.lean")
RUST = "src/decode/stages.rs"
MARKER = '/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize'
HEADER = '-- Checked original declarations after guarded slice lowering from original Execution::canonicalize.\nimport Arithmetic.ExecutionDriverGenerated\nimport BulksketchBridge.CanonicalizeOrdering\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.dupNamespace false\nset_option linter.unusedVariables false\n\nnamespace Aeneas.Std.CanonicalizeRuntime\n\nopen BulksketchBridge.CanonicalizeOrdering\n\nabbrev SortWords := core.cmp.Ord U64 → Slice U64 → Result (Slice U64)\n\ndef pairSlice (left right : U64) : Slice U64 :=\n  Slice.from [left, right] (by scalar_tac)\n\ndef scan {T C : Type} (callback : core.ops.function.FnMut C T Bool) :\n    List T → C → Result (Bool × Nat)\n  | [], _ => .ok (false, 0)\n  | item :: rest, state => do\n    let (found, state\') ← callback.call_mut state item\n    if found then .ok (true, 1) else\n      let (later, consumed) ← scan callback rest state\'\n      .ok (later, consumed + 1)\n\ndef anyShared {C : Type} (callback : core.ops.function.FnMut C U64 Bool)\n    (it : core.slice.iter.Iter U64) (state : C) :\n    Result (Bool × core.slice.iter.Iter U64) := do\n  let (found, consumed) ← scan callback (it.slice.val.drop it.i) state\n  .ok (found, { it with i := it.i + consumed })\n\ndef windows (words : Slice U64) (width : Usize) : Result (List (Slice U64)) :=\n  if width = 2#usize then .ok ((pairWindows words.val).map fun pair => pairSlice pair.1 pair.2)\n  else .fail .panic\n\ndef anyWindows {C : Type} (_ : Unit) (callback : core.ops.function.FnMut C (Slice U64) Bool)\n    (it : List (Slice U64)) (state : C) : Result (Bool × List (Slice U64)) := do\n  let (found, consumed) ← scan callback it state\n  .ok (found, it.drop consumed)\n\nend Aeneas.Std.CanonicalizeRuntime\n\nnamespace bulksketch\n\nvariable (sortModel : CanonicalizeRuntime.SortWords)\nlocal notation "core.slice.Slice.sort_unstable" => sortModel\nlocal notation "core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any" =>\n  CanonicalizeRuntime.anyShared\nlocal notation "core.slice.Slice.windows" => CanonicalizeRuntime.windows\nlocal notation "core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice" => (fun (_ : Type) => ())\nlocal notation "core.iter.traits.iterator.Iterator.any.default" => CanonicalizeRuntime.anyWindows\n\n'
FILES = {"Funs.lean", "Types.lean", "FunsExternal_Template.lean", "TypesExternal_Template.lean"}
CONTROLS = {"checked-replay": 0, "stock": 1, "wrong-guard": 1, "unchecked": 1, "unrelated": 0}
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar", "-print-error-emitters", "-split-files"]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def original_block(path):
    text = path.read_text()
    return text[text.index(MARKER):text.rindex("end bulksketch")]


def check(root=ROOT):
    receipt = json.loads((root / DIR / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-square/receipt.json").read_text())
    require(receipt["variant"] == "checked-canonicalize-slice-pattern-v1"
            and not receipt["native_source_edited"]
            and all(receipt[key] == parent[key] for key in ("source_commit", "rust_toolchain",
                                                          "target", "aeneas_commit", "charon_commit"))
            and all(receipt["tool_binary_sha256"][key] == parent["tool_binary_sha256"][key]
                    for key in ("aeneas", "charon")), "invalid canonicalize tool receipt")
    require(receipt["source_sha256"] == {RUST: sha(root.parents[1] / RUST)}
            and receipt["source_sha256"][RUST] == "93825fcb5054e98e9af060a81da72d4770c29354d79822ccfc949cc55f6e9b23",
            "frozen canonicalize Rust source differs")
    files = {str(DIR / "Arithmetic" / name) for name in FILES} | {
        str(DIR / name) for name in ("arithmetic.llbc", "charon.log", "checked.log",
           "checked-canonicalize-slice.patch", *(name + ".log" for name in CONTROLS))}
    require(set(receipt["artifacts"]) == files, "incomplete canonicalize receipt")
    for path, digest in receipt["artifacts"].items():
        require(sha(root / path) == digest, "canonicalize artifact differs: " + path)
    original = root / DIR / "arithmetic.llbc"
    digest = sha(original)
    require(digest == "c898e8ea9129de55f4ffab9f045f34b50b1252f3dcae106add6769a16fbf8ff5",
            "canonicalize original LLBC differs")
    llbc = json.loads(original.read_bytes())
    crate = llbc["translated"]
    opts = crate["options"]
    require(llbc["has_errors"] is False and opts["skip_borrowck"] is False
            and opts["start_from"] == ["bulksketch::decode::stages::_::canonicalize",
                                       "bulksketch::decode::affine::subspaces"]
            and opts["opaque"] == ["core::slice::_::sort_unstable"], "canonicalize LLBC capture scope differs")
    source = [f for f in crate["files"] if f and f["name"].get("Local") == RUST]
    require(len(source) == 1 and hashlib.sha256(source[0]["contents"].encode()).hexdigest() ==
            receipt["source_sha256"][RUST], "canonicalize embedded Rust source differs")
    decls = [fn for fn in crate["fun_decls"] if fn and
             fn["item_meta"]["name"][-1].get("Ident", [""])[0] == "canonicalize"]
    require(len(decls) == 1 and "Structured" in decls[0]["body"]
            and decls[0]["item_meta"]["span"]["Untagged"]["data"]["beg"]["line"] == 373,
            "canonicalize original source body differs")
    capture = receipt["capture"]
    require(capture["capture"] == 0 and capture["translation"] == 1 and
            "--no-dedup-serialized-ast" in capture["charon"], "canonicalize stock capture receipt differs")
    primary = receipt["primary"]
    output = {name: sha(root / DIR / "Arithmetic" / name) for name in FILES}
    require(primary["exit_code"] == 0 and primary["input_sha256"] == digest
            and primary["output_sha256"] == output
            and primary["command"][1:-2] == [*FLAGS, "-dest"]
            and primary["command"][-1] == capture["aeneas"][-1]
            and str(primary["command"][-1]) in (root / DIR / "checked.log").read_text(),
            "canonicalize checked original replay receipt differs")
    controls = receipt["controls"]
    require({key: value["exit_code"] for key, value in controls.items()} == CONTROLS,
            "canonicalize replay controls differ")
    for key, value in controls.items():
        expected_flags = [flag for flag in FLAGS if key != "unchecked" or flag != "-checks"]
        require(value["command"][1:-2] == [*expected_flags, "-dest"]
                and value["log_sha256"] == sha(root / DIR / (key + ".log")),
                "canonicalize control command differs: " + key)
    require(all(controls[key]["input_sha256"] == digest for key in ("stock", "checked-replay", "unchecked"))
            and controls["checked-replay"]["output_sha256"] == output
            and controls["wrong-guard"]["input_sha256"] != digest,
            "canonicalize replay original input differs")
    for key, message in {
        "stock": "Unsupported operation: &raw const (*roots)",
        "wrong-guard": "canonicalize slice lowering: length-two guard differs",
        "unchecked": "canonicalize slice lowering: symbolic and Rust borrow checks must be enabled",
    }.items():
        require(message in (root / DIR / (key + ".log")).read_text(), "canonicalize negative control differs: " + key)
    other = root / "extraction/avx-insert/horizontal"
    require(controls["unrelated"]["input_sha256"] == sha(other / "arithmetic.llbc")
            and controls["unrelated"]["output_sha256"] == {name: sha(other / "Arithmetic" / name) for name in FILES},
            "canonicalize unrelated replay differs")
    raw_types = original_block(root / DIR / "Arithmetic/Types.lean")
    raw_funs = original_block(root / DIR / "Arithmetic/Funs.lean")
    require((root / ACTIVE).read_text() == HEADER + raw_types + raw_funs + "end bulksketch\n",
            "compiled canonicalize projection differs")
    names = re.findall(r"(?m)^def\s+(decode\.stages\.Execution\.canonicalize[^\s]*)", raw_types + raw_funs)
    require(len(names) == len(set(names)) == 11 and "decode.stages.Execution.canonicalize" in names,
            "canonicalize projected declarations differ")
    return {"raw_generated_file": str(DIR / "Arithmetic/Funs.lean"),
            "raw_file_sha256": output["Funs.lean"],
            "compiled_projection": str(ACTIVE),
            "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": len(names),
            "generated_declarations": ["bulksketch." + name for name in names],
            "shared_types_and_function_dictionary_declarations_checked": True,
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
