#!/usr/bin/env python3
"""Check all three exact original decoder driver projections and their stock replay."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/native-driver")
ACTIVE = Path("bridge/Arithmetic/ExecutionDriverGenerated.lean")
SETUP = importlib.util.spec_from_file_location("driver_root_setup", ROOT / "extraction/root-setup/project.py")
setup = importlib.util.module_from_spec(SETUP)
SETUP.loader.exec_module(setup)
require, sha, declarations = setup.require, setup.sha, setup.declarations

HEADER = """-- Exact stock checked decoder driver declarations.
import Arithmetic.RootRunGenerated
import Arithmetic.BmLocatorGenerated
import Arithmetic.CandidateOuterGenerated
import Arithmetic.NativeDeflateGenerated
import Arithmetic.ExecutionVerifyGenerated

open Aeneas Aeneas.Std Result Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace Aeneas.Std.ExecutionDriverRuntime

open bulksketch.backend.contract bulksketch.decode.stages
open bulksketch.decode.scratch bulksketch.types

abbrev StageReply := core.result.Result (core.result.Result (Option Stage) DecodeFailure) DecodeError
abbrev Frame (F K : Type) :=
  StageReply × Execution F K × RowWorkspace × (RowWorkspace → RowWorkspace) × WorkMeter
abbrev Canonicalize :=
  ∀ {F K : Type}, bulksketch.field.BinaryField F → BulkKernels K F →
    Execution F K → RowWorkspace → WorkMeter → Result (Frame F K)

def optionEq {T : Type} (cmp : core.cmp.PartialEq T T) (left right : Option T) : Result Bool :=
  match left, right with
  | none, none => .ok true
  | some a, some b => cmp.eq a b
  | _, _ => .ok false

def resultMap {T E U F : Type} (callback : core.ops.function.FnOnce F T U)
    (value : core.result.Result T E) (function : F) : Result (core.result.Result U E) :=
  match value with
  | .Err error => .ok (.Err error)
  | .Ok input => do
    let output ← callback.call_once function input
    .ok (.Ok output)

def someValue {T : Type} (value : T) : Result (Option T) := .ok (some value)
def someCall {T : Type} (constructor : T → Result (Option T)) (value : T) : Result (Option T) :=
  constructor value

end Aeneas.Std.ExecutionDriverRuntime

namespace bulksketch

open ExecutionDriverRuntime

local notation "P.Insts.CoreOpsFunctionFnOnceTupleTOption.call_once" => someCall
local notation "core.option.Option.Some.constructor" => someValue
local notation "core.option.Option.Insts.CoreCmpPartialEqOption.eq" => optionEq
local notation "core.result.Result.map" => resultMap

"""

BINDINGS = """variable (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem)
variable (canonicalizeModel : Canonicalize)

local notation "decode.roots.Roots.run" => (decode.roots.Roots.run calls division)
local notation "decode.stages.Execution.canonicalize" => canonicalizeModel

"""

END = """
local notation "decode.stages.Execution.execute" => (decode.stages.Execution.execute calls division canonicalizeModel)

"""

STAGES = "bulksketch::decode::stages"
TRAIT = "{impl bulksketch::decode::row::RowExecution for bulksketch::decode::stages::Execution}"
MODELS = {
    "run-next": (TRAIT + "::run_next", "run_next", (414, 4, 441, 5),
                 [STAGES + "::_::execute", TRAIT + "::finish", TRAIT + "::next_stage"]),
    "next-stage": (TRAIT + "::next_stage", "next_stage", (408, 4, 413, 5),
                   [STAGES + "::_::execute", TRAIT + "::finish", TRAIT + "::run_next"]),
    "execute": (STAGES + "::_::execute", "execute", (166, 4, 240, 5),
                [STAGES + "::_::" + fn for fn in ("reconstruct", "candidates", "deflate", "verify", "canonicalize")] +
                ["bulksketch::decode::bm::locator", "bulksketch::decode::degree_probe::_::run",
                 "bulksketch::decode::degree_probe::_::count", "bulksketch::decode::roots::_::run"]),
}
LEAN_FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
              "-print-error-emitters", "-split-files"]
OUTPUTS = ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")
EXECUTION = "decode.stages.Execution"
DRIVER = EXECUTION + ".Insts.BulksketchDecodeRowRowExecution"
FN = "P.Insts.CoreOpsFunctionFnOnceTupleTOption"
PROGRESS = "decode.row.RowProgress"
TYPES = ("decode.stages.Execution", "decode.stages.State", "decode.row.RowInput",
         "decode.row.RowBudget", "decode.roots.Roots", "decode.scratch.RowWorkspace",
         "types.Stage", "types.DecodeFailure", "decode.degree_probe.DegreeProbe")


def checked_capture(root, mode, row, parent):
    selector, name, span, opaque = MODELS[mode]
    path = DIRECTORY / mode
    raw = root / path / "arithmetic.llbc"
    crate = json.loads(raw.read_text())
    translated = crate["translated"]
    opts = translated["options"]
    targets = translated["target_information"]
    require(crate["has_errors"] is False and opts["start_from"] == [selector] and opts["include"] == [selector]
            and opts["opaque"] == opaque and opts["skip_borrowck"] is False and len(targets) == 1
            and targets[0]["key"] == setup.TARGET and targets[0]["value"]["target_pointer_size"] == 8,
            "decoder driver original capture differs: " + mode)
    file_name = "src/decode/stages.rs"
    found = []
    for fn in translated["fun_decls"]:
        if not fn:
            continue
        meta = fn["item_meta"]
        source_span = meta["span"]["Untagged"]["data"]
        source = translated["files"][source_span["file_id"]]
        if source["name"] != {"Local": file_name} or meta["name"][-1].get("Ident", [None])[0] != name:
            continue
        begin, end = source_span["beg"], source_span["end"]
        found.append((begin["line"], begin["col"], end["line"], end["col"]))
        require(hashlib.sha256(source["contents"].encode()).hexdigest() == sha(root.parents[1] / file_name)
                and "Structured" in fn["body"], "decoder driver embedded original body differs: " + mode)
    require(found == [span], "decoder driver exact source span differs: " + mode)

    manifest = next(word for word in parent["charon_command"] if word.startswith("--manifest-path="))
    evidence = Path(manifest.removeprefix("--manifest-path=")).parent.parent / "bulksketch-proof-evidence-20261109-native-driver"
    output = evidence / mode
    capture = str(output / "arithmetic.llbc")
    require(opts["dest_file"] == capture and [step["step"] for step in row["commands"]] == ["charon", "stock", "replay"]
            and all(step["exit_code"] == 0 for step in row["commands"]),
            "decoder driver checked replay differs: " + mode)
    charon, stock, replay = row["commands"]
    require(charon["argv"] == [parent["charon_command"][0], "cargo", "--preset=aeneas", "--sysroot=default",
            "--dest-file=" + capture, "--start-from=" + selector, *("--opaque=" + item for item in opaque),
            "--include=" + selector, "--", manifest, "-p", "bulksketch", "--lib", "--locked", "--offline",
            "--target", setup.TARGET] and charon["environment"]["RUSTUP_TOOLCHAIN"] == "nightly-2026-09-17",
            "decoder driver Charon command differs: " + mode)
    for label, step in (("stock", stock), ("replay", replay)):
        require(step["argv"] == [parent["aeneas_command"][0], *LEAN_FLAGS, "-dest", str(output / label), capture]
                and step["environment"] == {} and "Generated:" in (root / path / (label + ".log")).read_text(),
                "decoder driver checked Aeneas command differs: " + mode)
    require(row["stock_replay_sha256"] == {name: sha(root / path / "Arithmetic" / name) for name in OUTPUTS},
            "decoder driver stock replay bytes differ: " + mode)
    types = declarations(root / path / "Arithmetic/Types.lean")
    common = declarations(root / "bridge/Arithmetic/ReconstructionTypes.lean")
    present = set(TYPES) & types.keys()
    needed = {EXECUTION, "decode.stages.State", "types.Stage"}
    if mode != "next-stage":
        needed |= {"decode.row.RowInput", "decode.scratch.RowWorkspace"}
    require(needed <= present and all(types[name] == common[name] for name in present),
            "decoder driver shared type differs: " + mode)


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/root-setup/receipt.json").read_text())
    require(receipt["source_commit"] == setup.SOURCE and receipt["aeneas_commit"] == setup.AENEAS
            and receipt["charon_commit"] == setup.CHARON and receipt["target"] == setup.TARGET
            and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["native_source_edited"] is False and receipt["native_llbc_edited"] is False
            and receipt["tools"] == {parent["charon_command"][0]: setup.BINARY_SHA256["charon"],
                parent["aeneas_command"][0]: setup.BINARY_SHA256["aeneas"]}
            and set(receipt["captures"]) == set(MODELS), "invalid decoder driver receipt")
    require(receipt["source"] == {name: sha(root.parents[1] / name) for name in
            ("src/decode/stages.rs", "src/decode/row.rs", "src/types.rs")}, "decoder driver frozen Rust source differs")
    artifacts = {str(DIRECTORY / mode / name) for mode in MODELS for name in
                 ("arithmetic.llbc", "charon.log", "stock.log", "replay.log",
                  *("Arithmetic/" + item for item in OUTPUTS))}
    require(set(receipt["artifacts"]) == artifacts, "decoder driver artifact list differs")
    for path, digest in receipt["artifacts"].items():
        require(sha(root / path) == digest, "decoder driver artifact differs: " + path)
    for mode, row in receipt["captures"].items():
        checked_capture(root, mode, row, parent)
    run_path = DIRECTORY / "run-next/Arithmetic/Funs.lean"
    next_path = DIRECTORY / "next-stage/Arithmetic/Funs.lean"
    exec_path = DIRECTORY / "execute/Arithmetic/Funs.lean"
    types = declarations(root / DIRECTORY / "run-next/Arithmetic/Types.lean")
    run = declarations(root / run_path)
    next_stage = declarations(root / next_path)
    execute = declarations(root / exec_path)
    expected = (HEADER + types[PROGRESS] + "\n\n" + execute[FN] + "\n\n" + BINDINGS
                + execute[EXECUTION + ".execute"] + "\n" + END + run[DRIVER + ".run_next"]
                + "\n\n" + next_stage[DRIVER + ".next_stage"] + "\n\nend bulksketch\n")
    require((root / ACTIVE).read_text() == expected, "compiled decoder driver projection differs")
    return {"raw_generated_file": str(exec_path), "raw_file_sha256": sha(root / exec_path),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": 5, "shared_types_and_function_dictionary_declarations_checked": True,
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
