#!/usr/bin/env python3
"""Check the original AVX recurrence entry and exact generated projection."""
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/avx-recurrence-entry")
ACTIVE = Path("bridge/Arithmetic/AvxRecurrenceEntryGenerated.lean")
RAW = DIRECTORY / "Arithmetic/Funs.lean"
TYPES = DIRECTORY / "Arithmetic/Types.lean"
SOURCE = "src/backend/x86_vpclmul512.rs"
MARKER = "/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::odd_recurrence_matches]:"
SELECTOR = "{impl bulksketch::backend::contract::BulkKernels for bulksketch::backend::x86_vpclmul512::Vpclmul512}::odd_recurrence_matches"
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar", "-print-error-emitters", "-split-files", "-dest"]
FILES = {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "replay.log",
    "Arithmetic/Funs.lean", "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean",
)}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def declaration(path, name):
    contents = path.read_text().split("end bulksketch", 1)[0]
    matches = [item.strip() for item in re.split(r"(?m)(?=^/--)", contents)
               if re.search(r"(?m)^(?:def|structure|axiom)\s+" + re.escape(name) + r"\s", item)]
    require(len(matches) == 1, "missing or repeated declaration " + name)
    return matches[0]


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-linear-entry/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in ("source_commit", "rust_toolchain",
        "target", "aeneas_commit", "charon_commit", "tool_binary_sha256"))
        and receipt["native_source_edited"] is False, "invalid AVX recurrence entry receipt")
    require(set(receipt["artifacts"]) == FILES, "incomplete AVX recurrence entry receipt")
    for file, digest in receipt["artifacts"].items():
        require(sha(root / file) == digest, "AVX recurrence entry artifact differs: " + file)
    require(sha(root / DIRECTORY / "arithmetic.llbc") ==
            "21ecc24ca45024c5f0ceb261626b04c2f302518d1f5ba169b483d7988e2d3dd4",
            "original AVX recurrence entry capture differs")
    require(sha(root / RAW) == "1ffdc96045cdac0c81f05bbada02a6efee73b6881ed98f88327de5b16986b957",
            "original AVX recurrence generated output differs")
    capture = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = capture["translated"]
    opts = crate["options"]
    require(capture["has_errors"] is False and opts["skip_borrowck"] is False
            and opts["start_from"] == opts["include"] == [SELECTOR], "AVX recurrence entry capture differs")
    expected_sources = {SOURCE, "src/backend/portable.rs", "src/backend/contract.rs"}
    require(set(receipt["source_sha256"]) == expected_sources, "incomplete AVX recurrence entry Rust sources")
    for source, digest in receipt["source_sha256"].items():
        matches = [file["contents"] for file in crate["files"] if file and file["name"] == {"Local": source}]
        require(len(matches) == 1 and sha256(matches[0].encode()).hexdigest() == digest
                and sha(root.parents[1] / source) == digest, "AVX recurrence entry Rust source differs: " + source)
    decls = {}
    for fn in crate["fun_decls"]:
        if fn and fn["item_meta"]["name"][-1].get("Ident", [""])[0] == "odd_recurrence_matches":
            span = fn["item_meta"]["span"]["Untagged"]["data"]
            if crate["files"][span["file_id"]]["name"] == {"Local": SOURCE}:
                decls[span["beg"]["line"]] = (span["end"]["line"], fn["body"])
    require(set(decls) == {124, 836} and decls[124][0] == 131 and "Structured" in decls[124][1]
            and decls[836] == (857, "Opaque"), "AVX recurrence entry source body or callee differs")
    ch, ae = (receipt["commands"][name] for name in ("charon", "aeneas"))
    replay = receipt["replay"]
    require(ch["exit_code"] == ae["exit_code"] == replay["exit_code"] == 0
            and ch["command"][4].removeprefix("--dest-file=") == ae["command"][-1] == replay["command"][-1]
            and ch["command"][-2:] == ["--target", receipt["target"]]
            and f"--start-from={SELECTOR}" in ch["command"] and f"--include={SELECTOR}" in ch["command"]
            and [arg.removeprefix("--opaque=") for arg in ch["command"] if arg.startswith("--opaque=")] == opts["opaque"]
            and ae["command"][1:-2] == replay["command"][1:-2] == FLAGS
            and replay["identical_outputs"] is True
            and replay["outputs_sha256"] == {name: sha(root / DIRECTORY / "Arithmetic" / name)
                for name in ("Funs.lean", "Types.lean", "FunsExternal_Template.lean")},
            "AVX recurrence entry checked replay differs")
    for name in ("default", "default_loop0", "default_loop0.body", "default_loop0_loop0",
                 "default_loop0_loop0.body"):
        qualified = "backend.contract.BulkKernels.odd_recurrence_matches." + name
        require(declaration(root / RAW, qualified) ==
                declaration(root / "bridge/Arithmetic/OddRecurrenceGenerated.lean", qualified),
                "AVX recurrence entry Portable default differs: " + name)
    for name, file in (
        ("field.BinaryField", "Types.lean"),
        ("backend.contract.Arithmetic", "SliceKernelTypes.lean"),
        ("backend.contract.BulkKernels", "SliceKernelTypes.lean"),
    ):
        current = declaration(root / "bridge/Arithmetic" / file, name)
        extracted = declaration(root / TYPES, name)
        start = "structure " + name
        require(current[current.index(start):] == extracted[extracted.index(start):],
                "AVX recurrence entry shared type differs: " + name)
    signature = declaration(root / DIRECTORY / "Arithmetic/FunsExternal_Template.lean",
                            "backend.x86_vpclmul512.odd_recurrence_matches")
    require(" ".join(signature[signature.index("axiom"):].split()) ==
            "axiom backend.x86_vpclmul512.odd_recurrence_matches : Slice Std.U64 → Slice Std.U64 → Result Bool",
            "AVX recurrence entry free signature differs")
    portable = "backend.portable.Portable"
    raw_portable = declaration(root / TYPES, portable)
    shared_portable = declaration(root / "bridge/Arithmetic/AvxLinearEntryGenerated.lean", portable)
    require(raw_portable.splitlines()[-1] in shared_portable.splitlines() and
            raw_portable.splitlines()[-1] == "def backend.portable.Portable := Unit",
            "AVX recurrence entry shared Portable type differs")
    raw = (root / RAW).read_text()
    require(raw.count(MARKER) == 1 and (root / ACTIVE).read_text() ==
            HEADER + raw[raw.index(MARKER):],
            "compiled AVX recurrence entry projection differs")
    return {"raw_generated_file": str(RAW), "raw_file_sha256": sha(root / RAW),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": 1,
            "generated_declarations": ["bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.odd_recurrence_matches"],
            "shared_types_and_function_dictionary_declarations_checked": True,
            "native_source_edited": False}


HEADER = '-- Original checked AVX odd_recurrence_matches backend entry.\nimport Arithmetic.AvxLinearEntryGenerated\nimport Arithmetic.AvxRecurrenceGenerated\nimport Arithmetic.OddRecurrenceGenerated\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\n\nnamespace bulksketch\n\nvariable (loadModel : AvxSquareRuntime.Load)\nvariable (portableModel : {F : Type} → field.BinaryField F → backend.contract.BulkKernels backend.portable.Portable F)\nlocal notation "backend.x86_vpclmul512.odd_recurrence_matches" =>\n  (backend.x86_vpclmul512.odd_recurrence_matches loadModel)\nlocal notation "backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels" => portableModel\n\n'

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
