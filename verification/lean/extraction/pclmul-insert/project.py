#!/usr/bin/env python3
"""Check the original PCLMUL insertion and exact generated projection."""
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/pclmul-insert")
ACTIVE = Path("bridge/Arithmetic/X86PclmulInsertGenerated.lean")
RAW = DIRECTORY / "Arithmetic/Funs.lean"
SOURCE = "src/backend/x86_pclmul.rs"
MARKER = "/-- [bulksketch::backend::x86_pclmul::insert]"
SELECTOR = "{impl bulksketch::backend::contract::BulkKernels for bulksketch::backend::x86_pclmul::Pclmul}::insert_nonzero"
NATIVE = "bulksketch::backend::x86_pclmul::insert"
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar", "-print-error-emitters", "-split-files", "-dest"]
FILES = {str(DIRECTORY / name) for name in (
    "arithmetic.llbc", "charon.log", "aeneas.log", "replay.log",
    "Arithmetic/Funs.lean", "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean", "Arithmetic/TypesExternal_Template.lean",
)}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-recurrence/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in ("source_commit", "rust_toolchain",
        "target", "aeneas_commit", "charon_commit", "tool_binary_sha256"))
        and receipt["native_source_edited"] is False, "invalid PCLMUL insertion receipt")
    require(set(receipt["artifacts"]) == FILES, "incomplete PCLMUL insertion receipt")
    for file, digest in receipt["artifacts"].items():
        require(sha(root / file) == digest, "PCLMUL insertion artifact differs: " + file)
    require(sha(root / DIRECTORY / "arithmetic.llbc") ==
            "5a796646cd2f8a83adc8d858b2a71569acdb036041c7b6015dece8db263ebcdb",
            "original PCLMUL insertion capture differs")
    require(sha(root / RAW) == "58f95ae2cdbdbc511316d8244e3ad52c27a3923d8e86ae05668408e331ebe0d5",
            "original PCLMUL insertion generated output differs")
    capture = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = capture["translated"]
    opts = crate["options"]
    require(capture["has_errors"] is False and opts["skip_borrowck"] is False
            and opts["start_from"] == [SELECTOR] and opts["include"] == [SELECTOR, NATIVE], "PCLMUL insertion capture differs")
    expected_sources = {SOURCE}
    require(set(receipt["source_sha256"]) == expected_sources, "incomplete PCLMUL insertion Rust sources")
    for source, digest in receipt["source_sha256"].items():
        matches = [file["contents"] for file in crate["files"] if file and file["name"] == {"Local": source}]
        require(len(matches) == 1 and sha256(matches[0].encode()).hexdigest() == digest
                and sha(root.parents[1] / source) == digest, "PCLMUL insertion Rust source differs: " + source)
    decls = {}
    for fn in crate["fun_decls"]:
        if fn and fn["item_meta"]["name"][-1].get("Ident", [""])[0] in {"insert", "insert_nonzero", "word", "low", "multiply", "reduced"}:
            span = fn["item_meta"]["span"]["Untagged"]["data"]
            if crate["files"][span["file_id"]]["name"] == {"Local": SOURCE}:
                decls[span["beg"]["line"]] = (span["end"]["line"], fn["body"])
    require(set(decls) == {98, 118, 124, 147, 160, 207} and decls[98][0] == 101 and "Structured" in decls[98][1]
            and decls[207][0] == 223 and "Structured" in decls[207][1]
            and [decls[line] for line in (118,124,147,160)] ==
                [(121,"Opaque"),(127,"Opaque"),(156,"Opaque"),(164,"Opaque")],
            "PCLMUL insertion original source body differs")
    ch, ae = (receipt["commands"][name] for name in ("charon", "aeneas"))
    replay = receipt["replay"]
    require(ch["exit_code"] == ae["exit_code"] == replay["exit_code"] == 0
            and ch["command"][4].removeprefix("--dest-file=") == ae["command"][-1] == replay["command"][-1]
            and ch["command"][-2:] == ["--target", receipt["target"]]
            and f"--start-from={SELECTOR}" in ch["command"]
            and [arg.removeprefix("--include=") for arg in ch["command"] if arg.startswith("--include=")] ==
                [SELECTOR, NATIVE]
            and [arg.removeprefix("--opaque=") for arg in ch["command"] if arg.startswith("--opaque=")] == opts["opaque"]
            and ae["command"][1:-2] == replay["command"][1:-2] == FLAGS
            and replay["identical_outputs"] is True
            and replay["outputs_sha256"] == {name: sha(root / DIRECTORY / "Arithmetic" / name)
                for name in ("Funs.lean", "Types.lean", "FunsExternal_Template.lean", "TypesExternal_Template.lean")},
            "PCLMUL insertion checked replay differs")
    require(set(receipt["shared_sha256"]) == set(SHARED), "incomplete PCLMUL insertion runtime link")
    for file, digest in receipt["shared_sha256"].items():
        require(sha(root / file) == digest, "PCLMUL insertion shared declaration differs: " + file)
    raw = (root / RAW).read_text()
    body = raw[raw.index(MARKER):]
    require(body.count(MARKER) == 5 and body.count("::insert_nonzero]:") == 1
            and "sorry" not in body, "PCLMUL insertion projected declaration count differs")
    external = (root / DIRECTORY / "Arithmetic/FunsExternal_Template.lean").read_text()
    for signature in (
        "axiom backend.x86_pclmul.low : core.core_arch.x86.__m128i → Result Std.U64",
        "axiom backend.x86_pclmul.word : Std.U64 → Result core.core_arch.x86.__m128i",
        "axiom backend.x86_pclmul.reduced {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F) : core.core_arch.x86.__m128i → Result core.core_arch.x86.__m128i",
        "axiom backend.x86_pclmul.multiply {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F) : Std.U64 → Std.U64 → Result Std.U64",
    ):
        require(signature in " ".join(external.split()), "PCLMUL insertion callee signature differs")
    require((root / ACTIVE).read_text() == HEADER + body, "compiled PCLMUL insertion projection differs")
    return {"raw_generated_file": str(RAW), "raw_file_sha256": sha(root / RAW),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": 6,
            "generated_declarations": ["bulksketch.backend.x86_pclmul." + name for name in ("insert_loop0_loop0.body", "insert_loop0_loop0", "insert_loop0.body", "insert_loop0", "insert", "Pclmul.Insts.BulksketchBackendContractBulkKernels.insert_nonzero")],
            "shared_types_and_function_dictionary_declarations_checked": True,
            "native_source_edited": False}


HEADER = '-- Original checked PCLMUL insertion and trait entry with exact register and slice bindings.\nimport Arithmetic.X86PclmulGenerated\nimport Arithmetic.PortableInsertionGenerated\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.dupNamespace false\nset_option linter.unusedVariables false\n\nnamespace bulksketch\n\nlocal notation "core.core_arch.x86.__m128i" => X86PclmulRuntime.Xmm\nlocal notation "core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128" => X86PclmulRuntime.clmul\n\n'
SHARED = ['bridge/Arithmetic/PortableInsertionGenerated.lean', 'bridge/Arithmetic/X86PclmulGenerated.lean']

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
