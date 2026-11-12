#!/usr/bin/env python3
"""Check the original AVX recurrence and exact generated projection."""
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/avx-recurrence")
ACTIVE = Path("bridge/Arithmetic/AvxRecurrenceGenerated.lean")
RAW = DIRECTORY / "Arithmetic/Funs.lean"
SOURCE = "src/backend/x86_vpclmul512.rs"
MARKER = "/-- [bulksketch::backend::x86_vpclmul512::odd_recurrence_matches]"
SELECTOR = "bulksketch::backend::x86_vpclmul512::odd_recurrence_matches"
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
    parent = json.loads((root / "extraction/avx-insert/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in ("source_commit", "rust_toolchain",
        "target", "aeneas_commit", "charon_commit", "tool_binary_sha256"))
        and receipt["native_source_edited"] is False, "invalid AVX recurrence receipt")
    require(set(receipt["artifacts"]) == FILES, "incomplete AVX recurrence receipt")
    for file, digest in receipt["artifacts"].items():
        require(sha(root / file) == digest, "AVX recurrence artifact differs: " + file)
    capture = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = capture["translated"]
    opts = crate["options"]
    require(capture["has_errors"] is False and opts["skip_borrowck"] is False
            and opts["start_from"] == [SELECTOR] and opts["include"] == [], "AVX recurrence capture differs")
    expected_sources = {SOURCE}
    require(set(receipt["source_sha256"]) == expected_sources, "incomplete AVX recurrence Rust sources")
    for source, digest in receipt["source_sha256"].items():
        matches = [file["contents"] for file in crate["files"] if file and file["name"] == {"Local": source}]
        require(len(matches) == 1 and sha256(matches[0].encode()).hexdigest() == digest
                and sha(root.parents[1] / source) == digest, "AVX recurrence Rust source differs: " + source)
    decls = {}
    for fn in crate["fun_decls"]:
        if fn and fn["item_meta"]["name"][-1].get("Ident", [""])[0] == "odd_recurrence_matches":
            span = fn["item_meta"]["span"]["Untagged"]["data"]
            if crate["files"][span["file_id"]]["name"] == {"Local": SOURCE}:
                decls[span["beg"]["line"]] = (span["end"]["line"], fn["body"])
    require(set(decls) == {836} and decls[836][0] == 857 and "Structured" in decls[836][1],
            "AVX recurrence original source body differs")
    ch, ae = (receipt["commands"][name] for name in ("charon", "aeneas"))
    replay = receipt["replay"]
    require(ch["exit_code"] == ae["exit_code"] == replay["exit_code"] == 0
            and ch["command"][4].removeprefix("--dest-file=") == ae["command"][-1] == replay["command"][-1]
            and ch["command"][-2:] == ["--target", receipt["target"]]
            and f"--start-from={SELECTOR}" in ch["command"]
            and [arg.removeprefix("--opaque=") for arg in ch["command"] if arg.startswith("--opaque=")] == opts["opaque"]
            and ae["command"][1:-2] == replay["command"][1:-2] == FLAGS
            and replay["identical_outputs"] is True, "AVX recurrence checked replay differs")
    require(set(receipt["shared_sha256"]) == SHARED, "incomplete AVX recurrence runtime link")
    for file, digest in receipt["shared_sha256"].items():
        require(sha(root / file) == digest, "AVX recurrence shared declaration differs: " + file)
    raw = (root / RAW).read_text()
    body = raw[raw.index(MARKER):]
    require(body.count(MARKER) == 5, "AVX recurrence projected declaration count differs")
    for name, suffix in (
        ("odd_recurrence_matches_loop0_loop0.body", ": loop 1:"),
        ("odd_recurrence_matches_loop0_loop0", ": loop body 0:"),
        ("odd_recurrence_matches_loop0.body", ": loop 0:"),
        ("odd_recurrence_matches_loop0", ":\n"),
    ):
        symbol = "backend.x86_vpclmul512." + name
        anchor = MARKER + suffix
        body = body.replace(anchor, f'local notation "{symbol}" => ({symbol} loadModel)\n\n' + anchor, 1)
    require((root / ACTIVE).read_text() == HEADER + body, "compiled AVX recurrence projection differs")
    return {"raw_generated_file": str(RAW), "raw_file_sha256": sha(root / RAW),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
            "source_declarations_retained_verbatim": 5,
            "shared_types_and_function_dictionary_declarations_checked": True,
            "native_source_edited": False}


HEADER = '-- Original stock checked AVX continuation with exact selected runtime bindings.\nimport Arithmetic.AvxSquareRuntime\nimport Arithmetic.X86LaneMaskGenerated\nimport BulksketchBridge.X86MaskedMemoryRegister\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.dupNamespace false\nset_option linter.unusedVariables false\n\nnamespace Aeneas.Std.AvxRecurrenceRuntime\n\nopen Avx512Register BulksketchBridge.X86MaskedMemory\n\ndef laneTest (left right : Word512) (lane : Fin 8) : Bool :=\n  decide (flatten left lane &&& flatten right lane ≠ 0)\n\ndef testMask (left right : Word512) : Result U8 :=\n  .ok ⟨BitVec.cast (by simp) (BitVec.ofBoolListLE (List.ofFn (laneTest left right)))⟩\n\nend Aeneas.Std.AvxRecurrenceRuntime\n\nnamespace bulksketch\n\nvariable (loadModel : AvxSquareRuntime.Load)\nlocal notation "core.core_arch.x86.__m512i" => Avx512Register.Word512\nlocal notation "backend.x86_vpclmul512.load" => loadModel\nlocal notation "core.core_arch.x86.avx512f._mm512_setzero_si512" => AvxSquareRuntime.zero\nlocal notation "core.core_arch.x86.avx512f._mm512_set1_epi64" => Avx512Register.broadcast\nlocal notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords\nlocal notation "core.core_arch.x86.avx512f._mm512_unpacklo_epi64" => Avx512Register.unpack false\nlocal notation "core.core_arch.x86.avx512f._mm512_test_epi64_mask" => AvxRecurrenceRuntime.testMask\nlocal notation "core.num.U64.to_ne_bytes" => X86PclmulRuntime.unsignedBytes\nlocal notation "core.num.I64.from_ne_bytes" => X86PclmulRuntime.signedFromBytes\n\n'
SHARED = {'bridge/Arithmetic/Avx512RegisterGenerated.lean', 'bridge/Arithmetic/X86LaneMaskGenerated.lean', 'bridge/Arithmetic/AvxSquareRuntime.lean', 'bridge/BulksketchBridge/X86MaskedMemoryRegister.lean'}

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
