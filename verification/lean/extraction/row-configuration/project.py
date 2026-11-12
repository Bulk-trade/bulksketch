#!/usr/bin/env python3
"""Check original checked row configuration and its generated declarations."""
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/row-configuration")
ACTIVE = Path("bridge/Arithmetic/RowConfigurationGenerated.lean")
RAW = DIRECTORY / "Arithmetic/Funs.lean"
SOURCE = "src/decode/stages.rs"
STAGES = "bulksketch::decode::stages"
BEGIN = f"{{impl bulksketch::decode::row::RowDecoder for {STAGES}::BinaryDecoder}}::begin"
METHODS = ("restart", "enable_v3", "start_degrees", "verification_count", "reject_upper", "set_splitter_seed")
SELECTORS = [BEGIN, *(f"{STAGES}::_::{name}" for name in METHODS)]
NAMES = ("decode.roots.Roots.Insts.CoreDefaultDefault.default",
         "decode.stages.BinaryDecoder.Insts.BulksketchDecodeRowRowDecoderFKExecution.begin",
         *(f"decode.stages.Execution.{name}" for name in
           ("set_splitter_seed", "restart", "enable_v3", "start_degrees", "verification_count", "reject_upper")))
SPANS = {"begin": (56, 75), "restart": (92, 95), "enable_v3": (97, 103),
         "start_degrees": (106, 113), "verification_count": (115, 117),
         "reject_upper": (120, 131), "set_splitter_seed": (159, 161)}
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest"]
FILES = {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "stock.log", "replay.log",
    "Arithmetic/Funs.lean", "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean",
)}
SHARED = {
    "bridge/Arithmetic/ExecutionDriverGenerated.lean",
    "bridge/Arithmetic/ReconstructionTypes.lean",
    "bridge/Arithmetic/RootSetupGenerated.lean",
    "bridge/Arithmetic/DegreeProbeGenerated.lean",
}


def require(test, message):
    if not test:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def project(raw):
    blocks = re.split(r"(?m)(?=^/--)", raw.split("end bulksketch", 1)[0])
    selected = []
    for name in NAMES:
        matches = [body.strip() for body in blocks if re.search(r"(?m)^def\s+" + re.escape(name) + r"\s", body)]
        require(len(matches) == 1, "row configuration original declaration differs: " + name)
        selected.append(matches[0])
    return HEADER + "\n\n".join(selected) + "\n\nend bulksketch\n"


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-insert/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in ("source_commit", "rust_toolchain",
        "target", "aeneas_commit", "charon_commit", "tool_binary_sha256"))
        and receipt["native_source_edited"] is False, "invalid row configuration receipt")
    require(set(receipt["artifacts"]) == FILES, "incomplete row configuration artifacts")
    for path, digest in receipt["artifacts"].items():
        require(sha(root / path) == digest, "row configuration artifact differs: " + path)
    require(set(receipt["shared_sha256"]) == SHARED, "incomplete row configuration shared declarations")
    for path, digest in receipt["shared_sha256"].items():
        require(sha(root / path) == digest, "row configuration shared declaration differs: " + path)
    capture = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = capture["translated"]
    opts = crate["options"]
    require(capture["has_errors"] is False and opts["skip_borrowck"] is False
            and opts["start_from"] == opts["include"] == SELECTORS, "row configuration capture differs")
    sources = {SOURCE, "src/decode/roots.rs", "src/decode/degree_probe.rs"}
    require(set(receipt["source_sha256"]) == sources, "incomplete row configuration Rust inputs")
    for path, digest in receipt["source_sha256"].items():
        original = [row["contents"] for row in crate["files"] if row and row["name"] == {"Local": path}]
        require(len(original) == 1 and sha256(original[0].encode()).hexdigest() == digest
                and sha(root.parents[1] / path) == digest, "row configuration original source differs: " + path)
    seen = {}
    for declaration in crate["fun_decls"]:
        if declaration and isinstance(declaration["body"], dict) and "Structured" in declaration["body"]:
            meta = declaration["item_meta"]
            span = meta["span"]["Untagged"]["data"]
            name = meta["name"][-1].get("Ident", [""])[0]
            if name and crate["files"][span["file_id"]]["name"] == {"Local": SOURCE}:
                seen[name] = (span["beg"]["line"], span["end"]["line"])
    require(seen == SPANS, "row configuration native source spans differ")
    charon, stock = receipt["commands"]
    replay = receipt["replay"]
    require(charon["exit_code"] == stock["exit_code"] == replay["exit_code"] == 0
            and charon["argv"][4].removeprefix("--dest-file=") == stock["argv"][-1] == replay["command"][-1]
            and stock["argv"][1:-2] == replay["command"][1:-2] == FLAGS
            and charon["argv"][-2:] == ["--target", receipt["target"]]
            and replay["outputs_sha256"] == {name: sha(root / DIRECTORY / "Arithmetic" / name)
                for name in ("Funs.lean", "Types.lean", "FunsExternal_Template.lean")},
            "row configuration checked replay differs")
    require((root / ACTIVE).read_text() == project((root / RAW).read_text()), "compiled row configuration projection differs")
    return {"raw_generated_file": str(RAW), "raw_file_sha256": sha(root / RAW),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": len(NAMES),
            "shared_types_and_function_dictionary_declarations_checked": True,
            "native_source_edited": False}


HEADER = '-- Exact original row initialization and configuration declarations.\nimport Arithmetic.ExecutionDriverGenerated\nimport Arithmetic.DegreeProbeGenerated\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.unusedVariables false\n\nnamespace bulksketch\n\nlocal notation "core.option.Option.Insts.CoreCmpPartialEqOption.eq" => ExecutionDriverRuntime.optionEq\n\n'

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
