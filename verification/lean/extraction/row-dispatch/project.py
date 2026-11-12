#!/usr/bin/env python3
"""Check original checked row dispatch and its generated declarations."""
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/row-dispatch")
ACTIVE = Path("bridge/Arithmetic/RowDispatchGenerated.lean")
RAW = DIRECTORY / "Arithmetic/Funs.lean"
SOURCE = "src/sketch/dispatch.rs"
PROBE = "src/decode/probe.rs"
METHODS = ("enable_v3", "start_degrees", "verification_count", "reject_upper", "next_stage", "run_next")
SELECTORS = [f"bulksketch::sketch::dispatch::_::{name}" for name in METHODS]
TYPES = ("backend.x86_pclmul.Pclmul", "backend.x86_vpclmul512.Vpclmul512",
         "decode.probe.Probe", "types.BackendId", "sketch.dispatch.DecodeExecution")
NAMES = ("decode.probe.Probe.next_stage", "decode.probe.Probe.impl.count", "decode.probe.Probe.reject",
         *(f"sketch.dispatch.DecodeExecution.{name}" for name in METHODS))
SPANS = {
    (SOURCE, "enable_v3"): (129, 138),
    (SOURCE, "start_degrees"): (140, 149),
    (SOURCE, "verification_count"): (150, 159),
    (SOURCE, "reject_upper"): (160, 169),
    (SOURCE, "next_stage"): (188, 197),
    (SOURCE, "run_next"): (199, 220),
    (PROBE, "next_stage"): (47, 49),
    (PROBE, "count"): (50, 52),
    (PROBE, "reject"): (58, 66),
}
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest"]
FILES = {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "stock.log", "replay.log",
    "Arithmetic/Funs.lean", "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean",
)}
SHARED = {f"bridge/Arithmetic/{name}.lean" for name in
          ("RowConfigurationGenerated", "AvxLinearEntryGenerated", "ExecutionDriverGenerated", "ReconstructionTypes")}



def require(test, message):
    if not test:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def declarations(raw, names, kind):
    blocks = re.split(r"(?m)(?=^/--)", raw.split("end bulksketch", 1)[0])
    selected = []
    for name in names:
        matches = [body.strip() for body in blocks if re.search(r"(?m)^" + kind + r"\s+" +
                  re.escape(name) + r"(?:\s|\()", body)]
        require(len(matches) == 1, "row dispatch original declaration differs: " + name)
        selected.append(matches[0])
    return "\n\n".join(selected)


def project(raw, types):
    return HEADER + declarations(types, TYPES, r"(?:def|structure|inductive)") + RUNTIME + \
        declarations(raw, NAMES, "def") + "\n\nend bulksketch\n"

def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-insert/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in ("source_commit", "rust_toolchain",
        "target", "aeneas_commit", "charon_commit", "tool_binary_sha256"))
        and receipt["native_source_edited"] is False, "invalid row dispatch receipt")
    require(set(receipt["artifacts"]) == FILES, "incomplete row dispatch artifacts")
    for path, digest in receipt["artifacts"].items():
        require(sha(root / path) == digest, "row dispatch artifact differs: " + path)
    require(set(receipt["shared_sha256"]) == SHARED, "incomplete row dispatch shared declarations")
    for path, digest in receipt["shared_sha256"].items():
        require(sha(root / path) == digest, "row dispatch shared declaration differs: " + path)
    capture = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = capture["translated"]
    opts = crate["options"]
    require(capture["has_errors"] is False and opts["skip_borrowck"] is False
            and opts["start_from"] == opts["include"] == SELECTORS, "row dispatch capture differs")
    sources = {SOURCE, PROBE}
    require(set(receipt["source_sha256"]) == sources, "incomplete row dispatch Rust inputs")
    for path, digest in receipt["source_sha256"].items():
        original = [row["contents"] for row in crate["files"] if row and row["name"] == {"Local": path}]
        require(len(original) == 1 and sha256(original[0].encode()).hexdigest() == digest
                and sha(root.parents[1] / path) == digest, "row dispatch original source differs: " + path)
    seen = {}
    for declaration in crate["fun_decls"]:
        if declaration and isinstance(declaration["body"], dict) and "Structured" in declaration["body"]:
            meta = declaration["item_meta"]
            span = meta["span"]["Untagged"]["data"]
            name = meta["name"][-1].get("Ident", [""])[0]
            path = crate["files"][span["file_id"]]["name"].get("Local")
            if name and path in sources:
                seen[(path, name)] = (span["beg"]["line"], span["end"]["line"])
    require(seen == SPANS, "row dispatch native source spans differ")
    charon, stock = receipt["commands"]
    replay = receipt["replay"]
    require(charon["exit_code"] == stock["exit_code"] == replay["exit_code"] == 0
            and charon["argv"][4].removeprefix("--dest-file=") == stock["argv"][-1] == replay["command"][-1]
            and stock["argv"][1:-2] == replay["command"][1:-2] == FLAGS
            and charon["argv"][-2:] == ["--target", receipt["target"]]
            and replay["outputs_sha256"] == {name: sha(root / DIRECTORY / "Arithmetic" / name)
                for name in ("Funs.lean", "Types.lean", "FunsExternal_Template.lean")},
            "row dispatch checked replay differs")
    require((root / ACTIVE).read_text() == project((root / RAW).read_text(),
            (root / DIRECTORY / "Arithmetic/Types.lean").read_text()), "compiled row dispatch projection differs")
    return {"raw_generated_file": str(RAW), "raw_file_sha256": sha(root / RAW),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": len(NAMES) + len(TYPES),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "native_source_edited": False}


HEADER = '-- Original checked decode-execution variant dispatch.\nimport Arithmetic.RowConfigurationGenerated\nimport Arithmetic.AvxLinearEntryGenerated\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.unusedVariables false\nset_option linter.dupNamespace false\n\nnamespace bulksketch\n\n'
RUNTIME = '\n\nend bulksketch\n\nnamespace Aeneas.Std.RowDispatchRuntime\n\nopen bulksketch.backend.contract bulksketch.backend.portable\nopen bulksketch.backend.x86_pclmul bulksketch.backend.x86_vpclmul512\nopen bulksketch.decode.probe bulksketch.decode.row bulksketch.types\n\nstructure Dictionaries where\n  portable : {F : Type} → bulksketch.field.BinaryField F → BulkKernels Portable F\n  pclmul : {F : Type} → bulksketch.field.BinaryField F → BulkKernels Pclmul F\n  vpclmul512 : {F : Type} → bulksketch.field.BinaryField F → BulkKernels Vpclmul512 F\n\nabbrev ProbeRun :=\n  {F : Type} → bulksketch.field.BinaryField F → BackendId → Probe →\n    Slice U64 → Slice U64 → Slice U64 → WorkMeter →\n    Result (core.result.Result RowProgress DecodeError × Probe × Slice U64 × Slice U64 × WorkMeter)\n\nend Aeneas.Std.RowDispatchRuntime\n\nnamespace bulksketch\n\nvariable (dictionaries : RowDispatchRuntime.Dictionaries)\nvariable (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem)\nvariable (canonicalize : ExecutionDriverRuntime.Canonicalize) (probeRun : RowDispatchRuntime.ProbeRun)\n\nlocal notation "backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels" => dictionaries.portable\nlocal notation "backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels" => dictionaries.pclmul\nlocal notation "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels" => dictionaries.vpclmul512\nlocal notation "decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.run_next" =>\n  (decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.run_next calls division canonicalize)\nlocal notation "sketch.dispatch.run_probe" => probeRun\n\n'

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
