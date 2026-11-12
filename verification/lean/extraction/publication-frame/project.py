#!/usr/bin/env python3
"""Check original checked publication frame and its generated declarations."""
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/publication-frame")
ACTIVE = Path("bridge/Arithmetic/PublicationFrameGenerated.lean")
RAW = DIRECTORY / "Arithmetic/Funs.lean"
SOURCE = "src/sketch/api.rs"
SELECTORS = [f"bulksketch::sketch::api::_::{name}" for name in ("new", "fail", "finish")]
SPANS = {"new": (243, 257), "fail": (314, 318), "finish": (321, 339)}
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest"]
FILES = {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "stock.log", "replay.log",
    "Arithmetic/Funs.lean", "Arithmetic/Types.lean",
)}
SHARED = {"bridge/Workmeter/Types.lean"}



def require(test, message):
    if not test:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def project(raw, raw_types):
    types = raw_types[raw_types.index("namespace bulksketch"):raw_types.index("end bulksketch")]
    blocks = re.split(r"(?m)(?=^/--)", types)
    retained = "".join(block for block in blocks if "def types.WorkUnits" not in block
                       and "inductive types.DecodeError" not in block)
    return HEADER + retained.replace("namespace bulksketch\n",
        'namespace bulksketch\n\nlocal notation "fail" => Result.fail\n', 1) + raw[raw.index("/-- [bulksketch::sketch::api::"):]

def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-insert/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in ("source_commit", "rust_toolchain",
        "target", "aeneas_commit", "charon_commit", "tool_binary_sha256"))
        and receipt["native_source_edited"] is False, "invalid publication frame receipt")
    require(set(receipt["artifacts"]) == FILES, "incomplete publication frame artifacts")
    for path, digest in receipt["artifacts"].items():
        require(sha(root / path) == digest, "publication frame artifact differs: " + path)
    require(set(receipt["shared_sha256"]) == SHARED, "incomplete publication frame shared declarations")
    for path, digest in receipt["shared_sha256"].items():
        require(sha(root / path) == digest, "publication frame shared declaration differs: " + path)
    capture = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = capture["translated"]
    opts = crate["options"]
    require(capture["has_errors"] is False and opts["skip_borrowck"] is False
            and opts["start_from"] == opts["include"] == SELECTORS, "publication frame capture differs")
    sources = {SOURCE, "src/sketch/scratch.rs", "src/types.rs"}
    require(set(receipt["source_sha256"]) == sources, "incomplete publication frame Rust inputs")
    for path, digest in receipt["source_sha256"].items():
        original = [row["contents"] for row in crate["files"] if row and row["name"] == {"Local": path}]
        require(len(original) == 1 and sha256(original[0].encode()).hexdigest() == digest
                and sha(root.parents[1] / path) == digest, "publication frame original source differs: " + path)
    seen = {}
    for declaration in crate["fun_decls"]:
        if declaration and isinstance(declaration["body"], dict) and "Structured" in declaration["body"]:
            meta = declaration["item_meta"]
            span = meta["span"]["Untagged"]["data"]
            name = meta["name"][-1].get("Ident", [""])[0]
            if name in SPANS and crate["files"][span["file_id"]]["name"] == {"Local": SOURCE}:
                seen[name] = (span["beg"]["line"], span["end"]["line"])
    require(seen == SPANS, "publication frame native source spans differ")
    charon, stock = receipt["commands"]
    replay = receipt["replay"]
    require(charon["exit_code"] == stock["exit_code"] == replay["exit_code"] == 0
            and charon["argv"][4].removeprefix("--dest-file=") == stock["argv"][-1] == replay["command"][-1]
            and stock["argv"][1:-2] == replay["command"][1:-2] == FLAGS
            and charon["argv"][-2:] == ["--target", receipt["target"]]
            and replay["outputs_sha256"] == {name: sha(root / DIRECTORY / "Arithmetic" / name)
                for name in ("Funs.lean", "Types.lean")},
            "publication frame checked replay differs")
    compiled = project((root / RAW).read_text(), (root / DIRECTORY / "Arithmetic/Types.lean").read_text())
    require((root / ACTIVE).read_text() == compiled, "compiled publication frame projection differs")
    count = len(re.findall(r"(?m)^(?:def|structure|inductive) sketch\.", compiled))
    require(count == 13, "publication frame retained declaration count differs")
    return {"raw_generated_file": str(RAW), "raw_file_sha256": sha(root / RAW),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": count,
            "shared_types_and_function_dictionary_declarations_checked": True,
            "native_source_edited": False}


HEADER = '-- Original checked publication frame declarations.\nimport Workmeter.Types\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.unusedVariables false\nset_option linter.dupNamespace false\n\n'

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
