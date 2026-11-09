#!/usr/bin/env python3
"""Check the original AVX linear-update entry and exact generated projection."""
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/avx-linear-entry")
ACTIVE = Path("bridge/Arithmetic/AvxLinearEntryGenerated.lean")
RAW = DIRECTORY / "Arithmetic/Funs.lean"
TYPES = DIRECTORY / "Arithmetic/Types.lean"
SOURCE = "src/backend/x86_vpclmul512.rs"
MARKER = "/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::multiply_linear]:"
SELECTOR = "{impl bulksketch::backend::contract::BulkKernels for bulksketch::backend::x86_vpclmul512::Vpclmul512}::multiply_linear"
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
    parent = json.loads((root / "extraction/avx-insert/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in ("source_commit", "rust_toolchain",
        "target", "aeneas_commit", "charon_commit", "tool_binary_sha256"))
        and receipt["native_source_edited"] is False, "invalid AVX linear entry receipt")
    require(set(receipt["artifacts"]) == FILES, "incomplete AVX linear entry receipt")
    for file, digest in receipt["artifacts"].items():
        require(sha(root / file) == digest, "AVX linear entry artifact differs: " + file)
    capture = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = capture["translated"]
    opts = crate["options"]
    require(capture["has_errors"] is False and opts["skip_borrowck"] is False
            and opts["start_from"] == opts["include"] == [SELECTOR], "AVX linear entry capture differs")
    expected_sources = {SOURCE, "src/backend/portable.rs", "src/backend/contract.rs"}
    require(set(receipt["source_sha256"]) == expected_sources, "incomplete AVX linear entry Rust sources")
    for source, digest in receipt["source_sha256"].items():
        matches = [file["contents"] for file in crate["files"] if file and file["name"] == {"Local": source}]
        require(len(matches) == 1 and sha256(matches[0].encode()).hexdigest() == digest
                and sha(root.parents[1] / source) == digest, "AVX linear entry Rust source differs: " + source)
    decls = {}
    for fn in crate["fun_decls"]:
        if fn and fn["item_meta"]["name"][-1].get("Ident", [""])[0] == "multiply_linear":
            span = fn["item_meta"]["span"]["Untagged"]["data"]
            if crate["files"][span["file_id"]]["name"] == {"Local": SOURCE}:
                decls[span["beg"]["line"]] = (span["end"]["line"], fn["body"])
    require(set(decls) == {116, 820} and decls[116][0] == 122 and "Structured" in decls[116][1]
            and decls[820] == (833, "Opaque"), "AVX linear entry source body or callee differs")
    ch, ae = (receipt["commands"][name] for name in ("charon", "aeneas"))
    replay = receipt["replay"]
    require(ch["exit_code"] == ae["exit_code"] == replay["exit_code"] == 0
            and ch["command"][4].removeprefix("--dest-file=") == ae["command"][-1] == replay["command"][-1]
            and ch["command"][-2:] == ["--target", receipt["target"]]
            and f"--start-from={SELECTOR}" in ch["command"] and f"--include={SELECTOR}" in ch["command"]
            and [arg.removeprefix("--opaque=") for arg in ch["command"] if arg.startswith("--opaque=")] == opts["opaque"]
            and ae["command"][1:-2] == replay["command"][1:-2] == FLAGS
            and replay["identical_outputs"] is True, "AVX linear entry checked replay differs")
    for name in ("default", "default_loop", "default_loop.body"):
        qualified = "backend.contract.BulkKernels.multiply_linear." + name
        require(declaration(root / RAW, qualified) ==
                declaration(root / "bridge/Arithmetic/SliceKernelGenerated.lean", qualified),
                "AVX linear entry Portable default differs: " + name)
    for name, file in (
        ("field.BinaryField", "Types.lean"),
        ("backend.contract.Arithmetic", "SliceKernelTypes.lean"),
        ("backend.contract.BulkKernels", "SliceKernelTypes.lean"),
    ):
        current = declaration(root / "bridge/Arithmetic" / file, name)
        extracted = declaration(root / TYPES, name)
        start = "structure " + name
        require(current[current.index(start):] == extracted[extracted.index(start):],
                "AVX linear entry shared type differs: " + name)
    signature = declaration(root / DIRECTORY / "Arithmetic/FunsExternal_Template.lean",
                            "backend.x86_vpclmul512.multiply_linear")
    require(" ".join(signature[signature.index("axiom"):].split()) ==
            "axiom backend.x86_vpclmul512.multiply_linear : Slice Std.U64 → Std.U64 → Result (Slice Std.U64)",
            "AVX linear entry free signature differs")
    kind = declaration(root / TYPES, "backend.portable.Portable")
    raw = (root / RAW).read_text()
    require(raw.count(MARKER) == 1 and (root / ACTIVE).read_text() ==
            HEADER + kind + "\n\n" + BINDINGS + raw[raw.index(MARKER):],
            "compiled AVX linear entry projection differs")
    return {"raw_generated_file": str(RAW), "raw_file_sha256": sha(root / RAW),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": 2,
            "shared_types_and_function_dictionary_declarations_checked": True,
            "native_source_edited": False}


HEADER = '-- Original checked AVX multiply_linear backend entry.\nimport Arithmetic.AvxMultiplyLinearGenerated\nimport Arithmetic.SliceKernelGenerated\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\n\nnamespace bulksketch\n\n'
BINDINGS = 'variable (loadModel : AvxSquareRuntime.Load) (storeModel : AvxSquareRuntime.Store)\nvariable (portableModel : {F : Type} → field.BinaryField F → backend.contract.BulkKernels backend.portable.Portable F)\nlocal notation "backend.x86_vpclmul512.multiply_linear" =>\n  (backend.x86_vpclmul512.multiply_linear loadModel storeModel)\nlocal notation "backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels" => portableModel\n\n'

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
