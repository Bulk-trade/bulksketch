#!/usr/bin/env python3
"""Check the original AVX scalar delegate and exact generated projection."""
from hashlib import sha256
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/avx-scalar-delegates")
ACTIVE = Path("bridge/Arithmetic/AvxScalarDelegatesGenerated.lean")
RAW = DIRECTORY / "Arithmetic/Funs.lean"
AVX = "src/backend/x86_vpclmul512.rs"
PCLMUL = "src/backend/x86_pclmul.rs"
SELECTORS = ["{impl bulksketch::backend::contract::Arithmetic for "
             "bulksketch::backend::x86_vpclmul512::Vpclmul512}::" + name
             for name in ("mul", "square", "frobenius", "inverse", "trace",
                          "solve_quadratic", "raw_mul", "reduce")]
SPANS = {
    (AVX, name, line, line + 2)
    for name, line in zip(("mul", "square", "frobenius", "inverse", "trace",
                           "solve_quadratic", "raw_mul", "reduce"), range(50, 74, 3), strict=True)
} | {(PCLMUL, "trace", 59, 61), (PCLMUL, "reduce", 73, 75)}
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


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-insert/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in ("source_commit", "rust_toolchain",
        "target", "aeneas_commit", "charon_commit", "tool_binary_sha256"))
        and receipt["native_source_edited"] is False, "invalid AVX scalar delegate receipt")
    require(set(receipt["artifacts"]) == FILES, "incomplete AVX scalar delegate receipt")
    for file, digest in receipt["artifacts"].items():
        require(sha(root / file) == digest, "AVX scalar delegate artifact differs: " + file)
    capture = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = capture["translated"]
    opts = crate["options"]
    require(capture["has_errors"] is False and opts["skip_borrowck"] is False
            and opts["start_from"] == opts["include"] == SELECTORS, "AVX scalar delegate capture differs")
    expected_sources = {AVX, PCLMUL}
    require(set(receipt["source_sha256"]) == expected_sources, "incomplete AVX scalar delegate Rust sources")
    for source, digest in receipt["source_sha256"].items():
        matches = [file["contents"] for file in crate["files"] if file and file["name"] == {"Local": source}]
        require(len(matches) == 1 and sha256(matches[0].encode()).hexdigest() == digest
                and sha(root.parents[1] / source) == digest, "AVX scalar delegate Rust source differs: " + source)
    decls = set()
    for fn in crate["fun_decls"]:
        if fn and isinstance(fn["body"], dict) and "Structured" in fn["body"]:
            span = fn["item_meta"]["span"]["Untagged"]["data"]
            name = fn["item_meta"]["name"][-1].get("Ident", [""])[0]
            path = crate["files"][span["file_id"]]["name"].get("Local")
            if path in expected_sources and name != "clone":
                decls.add((path, name, span["beg"]["line"], span["end"]["line"]))
    require(decls == SPANS, "AVX scalar delegate source bodies differ")
    ch, ae = (receipt["commands"][name] for name in ("charon", "aeneas"))
    replay = receipt["replay"]
    require(ch["exit_code"] == ae["exit_code"] == replay["exit_code"] == 0
            and ch["command"][4].removeprefix("--dest-file=") == ae["command"][-1] == replay["command"][-1]
            and ch["command"][-2:] == ["--target", receipt["target"]]
            and [f"--start-from={selector}" for selector in SELECTORS] == ch["command"][5:13]
            and [arg.removeprefix("--opaque=") for arg in ch["command"] if arg.startswith("--opaque=")] == opts["opaque"]
            and ae["command"][1:-2] == replay["command"][1:-2] == FLAGS
            and replay["identical_outputs"] is True, "AVX scalar delegate checked replay differs")
    require(set(receipt["shared_sha256"]) == SHARED, "incomplete AVX scalar delegate runtime link")
    for file, digest in receipt["shared_sha256"].items():
        require(sha(root / file) == digest, "AVX scalar delegate shared declaration differs: " + file)
    raw = (root / RAW).read_text()
    body = raw[raw.index("namespace bulksketch"):]
    names = re.findall(r"(?m)^def\s+(backend\.x86_\w+\.\S+)", body)
    require(len(names) == len(set(names)) == 10, "AVX scalar delegate declaration count differs")
    require((root / ACTIVE).read_text() == HEADER + body, "compiled AVX scalar delegate projection differs")
    return {"raw_generated_file": str(RAW), "raw_file_sha256": sha(root / RAW),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": 10,
            "shared_types_and_function_dictionary_declarations_checked": True,
            "native_source_edited": False,
            "generated_declarations": ["bulksketch." + name for name in names]}


HEADER = '-- Original checked PCLMUL and AVX scalar delegation declarations.\nimport Arithmetic.X86PclmulNextGenerated\nimport Arithmetic.Funs\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\n\n'
SHARED = {'bridge/Arithmetic/X86PclmulNextGenerated.lean', 'bridge/Arithmetic/Funs.lean', 'bridge/Arithmetic/Types.lean', 'bridge/Arithmetic/X86PclmulGenerated.lean'}

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
