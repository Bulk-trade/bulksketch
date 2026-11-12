#!/usr/bin/env python3
"""Verify the frozen affine solve_map declarations and existing scalar bindings."""
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/affine-solve-map")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/AffineSolveMapGenerated.lean")
SHARED = [Path("bridge/Arithmetic/Types.lean"), Path("bridge/Arithmetic/SliceKernelTypes.lean")]
SOURCE = Path("src/decode/affine.rs")
SOURCE_SHA = {'src/decode/affine.rs': 'a7c45498717202aec291b4c4acdd6f819edf16bcdf478500a8c74a3492c4e11d', 'src/field/mod.rs': '035dc6193ebb50b324527525c0ee47cbe06ca325db16aa5f8ee55b0e79baa723', 'src/backend/contract.rs': '4d05ce564edc408ba04f5a907b159ad91018ba8cfd93126e17913ed49f7e3d59'}
BODY_START = "/-- [bulksketch::decode::affine::square_column]"
TOOL_COMMITS = {
    "charon_commit": "7b462d9159db2ed3015162352183906a30bfafc6",
    "aeneas_commit": "ab34bd28458a08c150b7cbf1873e59af74588138",
}
TOOL_DIGESTS = {
    "charon": "913e7969d1a0296038d115bcf1af47f8c0c6702266cc7a78a02a2b4ad7a0dfbe",
    "aeneas": "91f5a2776a79e2923517a2c4807c9fc017e79f185ae490502247f16e2941e330",
}
RUST_ROOTS = ["bulksketch::decode::affine::solve_map"]
RUST_SPANS = {
    "solve_map": (175, 0, 232, 1),
    "frobenius_columns": (353, 0, 370, 1),
    "square_column": (372, 0, 388, 1),
}
AENEAS_FLAGS = [
    "-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
    "-print-error-emitters", "-split-files", "-dest",
]
HEADER = '-- Stock-checked original affine map with its native Frobenius column initializer.\nimport Arithmetic.AffineSubspacesGenerated\nimport Arithmetic.MutableZipRuntime\nimport Arithmetic.AffineEnumerateGenerated\nimport Arithmetic.TrailingZeros\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\n\nset_option linter.unusedVariables false\nset_option maxRecDepth 4096\n\nnamespace bulksketch\n\ndef AffineSolveMapRuntime.trailingZeros (word : U64) : Result U32 :=\n  .ok ⟨word.bv.ctz.setWidth 32⟩\n\nlocal notation "core.num.U64.trailing_zeros" => AffineSolveMapRuntime.trailingZeros\n\n'


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def body(path):
    return path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]


def project(selected):
    marker = "/-- [bulksketch::decode::affine::solve_map]"
    for section, which, notation in [
        ("MutableStep", ": loop body 2:",
         'local notation "core.iter.adapters.enumerate.IteratorEnumerate.next" => Aeneas.Std.MutableEnumerate.next'),
        ("MutableConstruct", ": loop body 0:",
         'local notation "core.iter.traits.iterator.Iterator.enumerate.trait_default" => Aeneas.Std.MutableEnumerate.construct'),
    ]:
        start = selected.index(marker + which)
        stop = selected.index(marker, start + len(marker))
        selected = (selected[:start] + f"section {section}\n{notation}\n\n" + selected[start:stop] +
                    f"end {section}\n\n" + selected[stop:])
    return HEADER + selected + "end bulksketch\n"


def check_replay(root, receipt):
    if (any(receipt[name] != commit for name, commit in TOOL_COMMITS.items()) or
            receipt["tool_binary_sha256"] != TOOL_DIGESTS or
            receipt["rust_toolchain"] != "nightly-2026-09-17" or
            receipt["target"] != "x86_64-apple-darwin" or receipt["selected_roots"] != RUST_ROOTS):
        raise ValueError("affine solve_map extraction tool identity differs")
    commands = receipt["commands"]
    if len(commands) != 3 or any(command["exit_code"] != 0 for command in commands):
        raise ValueError("affine solve_map checked extraction did not complete")
    capture, initial, replay = (command["command"] for command in commands)
    if (Path(capture[0]).name != "charon" or capture[1:4] != ["cargo", "--preset=aeneas", "--sysroot=default"] or
            [arg for arg in capture if arg.startswith("--start-from=")] != [
                "--start-from=" + name for name in RUST_ROOTS] or
            any(arg.startswith(("--opaque=", "--exclude=")) for arg in capture) or
            capture[-2:] != ["--target", "x86_64-apple-darwin"]):
        raise ValueError("affine solve_map Charon selector differs")
    for command, directory in ((initial, "checked"), (replay, "replay")):
        if (len(command) != 11 or Path(command[0]).name != "main.exe" or
                command[1:9] != AENEAS_FLAGS or Path(command[9]).name != directory or
                Path(command[10]).name != "arithmetic.llbc" or command[10] != initial[10]):
            raise ValueError("affine solve_map requires original checked extraction")
    files = {name: digest(root / RAW / name)
             for name in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")}
    if receipt["checked_replay_byte_identical"] is not True or receipt["replay_generated_sha256"] != files:
        raise ValueError("affine solve_map replay does not match")


def check_llbc(root):
    capture = json.loads((root / DIRECTORY / "arithmetic.llbc").read_bytes())
    if capture["has_errors"] is not False:
        raise ValueError("incomplete affine solve_map LLBC")
    translated = capture["translated"]
    for name, expected in SOURCE_SHA.items():
        sources = [file for file in translated["files"] if file and file["name"] == {"Local": name}]
        if len(sources) != 1 or sha256(sources[0]["contents"].encode()).hexdigest() != expected:
            raise ValueError("affine solve_map capture changed its embedded Rust source: " + name)
    affine_source = next(file for file in translated["files"] if file and file["name"] == {"Local": str(SOURCE)})
    for name, expected in RUST_SPANS.items():
        qualified = [{"Ident": [part, 0]} for part in ("bulksketch", "decode", "affine", name)]
        functions = [fun for fun in translated["fun_decls"] if fun and fun["item_meta"]["name"] == qualified]
        if len(functions) != 1 or set(functions[0]["body"]) != {"Structured"}:
            raise ValueError("missing structured affine solve_map body: " + name)
        span = functions[0]["item_meta"]["span"]["Untagged"]
        data = span["data"]
        actual = (data["beg"]["line"], data["beg"]["col"], data["end"]["line"], data["end"]["col"])
        if data["file_id"] != affine_source["id"] or span["generated_from_span"] is not None or actual != expected:
            raise ValueError("affine solve_map body span differs: " + name)


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    artifacts = receipt["artifacts"]
    expected = {str(RAW / name) for name in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")}
    expected.update(str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log", "replay.log"))
    if (receipt["status"] != "generated" or receipt["llbc_has_errors"] is not False or
            receipt["native_source_edited"] is not False or len(artifacts) != len(expected) or
            {item["path"] for item in artifacts} != expected):
        raise ValueError("incomplete affine solve_map extraction receipt")
    for item in artifacts:
        if digest(root / item["path"]) != item["sha256"]:
            raise ValueError("affine solve_map extraction mismatch: " + item["path"])
    if (receipt["source_sha256"] != SOURCE_SHA or
            any(digest(root.parents[1] / name) != expected for name, expected in SOURCE_SHA.items())):
        raise ValueError("frozen affine solve_map source differs")
    check_replay(root, receipt)
    check_llbc(root)
    types = re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body(root / RAW / "Types.lean"))
    shared = [(root / name).read_text() for name in SHARED]
    if len(types) != 6 or any(not any(block.strip() in file for file in shared) for block in types):
        raise ValueError("affine solve_map shared generated type differs")
    externals = re.findall(r"(?m)^axiom\s+(\S+)", (root / RAW / "FunsExternal_Template.lean").read_text())
    if externals != ["core.num.U64.trailing_zeros", "core.slice.raw.from_ref"]:
        raise ValueError("affine solve_map external binding set changed")
    raw = RAW / "Funs.lean"
    raw_body = body(root / raw)
    selected = raw_body[raw_body.index(BODY_START):]
    names = re.findall(r"(?m)^def\s+(\S+)", selected)
    if (len(names) != 26 or len(set(names)) != 26 or not all(name.startswith("decode.affine.") for name in names) or
            "core.slice.raw.from_ref" in selected or "sorry" in selected):
        raise ValueError("affine solve_map declaration set changed")
    if (root / ACTIVE).read_text() != project(selected):
        raise ValueError("compiled affine solve_map projection differs")
    return {"raw_generated_file": str(raw), "raw_file_sha256": digest(root / raw),
            "compiled_projection": str(ACTIVE), "projection_file_sha256": digest(root / ACTIVE),
            "source_declarations_retained_verbatim": len(names),
            "generated_declarations": ["bulksketch." + name for name in names],
            "shared_types_and_function_dictionary_declarations_checked": True,
            "native_source_edited": False}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
