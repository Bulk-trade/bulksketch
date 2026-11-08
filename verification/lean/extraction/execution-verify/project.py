#!/usr/bin/env python3
"""Check the source-pinned Execution::verify declaration and its exact dependencies."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = Path("extraction/execution-verify")
RAW = EXTRACTION / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/ExecutionVerifyGenerated.lean")
SOURCE_COMMIT = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
AENEAS_COMMIT = "ab34bd28458a08c150b7cbf1873e59af74588138"
CHARON_COMMIT = "7b462d9159db2ed3015162352183906a30bfafc6"
TARGET = "x86_64-apple-darwin"
NAME = "decode.stages.Execution.verify"
STAGES = "bulksketch::decode::stages"
INCLUDE = STAGES + "::_::verify"
OPAQUE = [
    STAGES + "::_::_",
    STAGES + "::check_workspace",
    "bulksketch::decode::verify::rebuilt_lfsr",
    "bulksketch::decode::verify::use_rebuilt_lfsr",
    "bulksketch::decode::probe::verified",
]
SOURCES = {
    "verify": ("src/decode/stages.rs", 334, 4, 372, 5),
    "charge": ("src/decode/stages.rs", 163, 4, 165, 5),
    "rebuilt_lfsr": ("src/decode/verify.rs", 75, 0, 99, 1),
    "use_rebuilt_lfsr": ("src/decode/verify.rs", 57, 0, 67, 1),
    "verified": ("src/decode/probe.rs", 168, 0, 183, 1),
}
CALLS = {
    "decode.stages.Execution.charge": "bridge/Arithmetic/WorkScheduleGenerated.lean",
    "decode.verify.rebuilt_lfsr": "bridge/Arithmetic/RebuiltLfsrGenerated.lean",
    "decode.verify.use_rebuilt_lfsr": "bridge/Arithmetic/VerifyDispatchGenerated.lean",
    "decode.probe.verified": "bridge/Arithmetic/DegreeProbeGenerated.lean",
}
TYPE_DEPENDENCIES = {
    "bridge/Arithmetic/Types.lean": ("types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"),
    "bridge/Arithmetic/SliceKernelTypes.lean": ("backend.contract.Arithmetic", "backend.contract.BulkKernels"),
    "bridge/Workmeter/Types.lean": ("types.WorkUnits", "types.WorkMeter", "types.DecodeError"),
    "bridge/Arithmetic/WorkScheduleGenerated.lean": ("decode.work.Charge",),
    "bridge/Arithmetic/ReconstructionTypes.lean": (
        "core.marker.PhantomData", "types.Stage", "decode.degree_probe.DegreeProbe", "decode.roots.Roots",
        "types.DecodeFailure", "decode.row.RowBudget", "decode.row.RowInput", "decode.scratch.FactorFrame",
        "decode.scratch.SplitterBasis", "decode.scratch.RowWorkspace", "decode.stages.State", "decode.stages.Execution",
    ),
}
ARTIFACTS = {
    "arithmetic.llbc", "charon.log", "pinned.log", "Arithmetic/Types.lean",
    "Arithmetic/Funs.lean", "Arithmetic/FunsExternal_Template.lean",
}
HEADER = """-- Original Execution::verify declaration with imports of separately checked callees.
import Arithmetic.DegreeProbeGenerated
import Arithmetic.VerifyDispatchGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

"""


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def declarations(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[-1].rsplit("end bulksketch", 1)[0]
    items = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        names = re.findall(r"(?m)^(?:def|impl_def|structure|inductive|abbrev|axiom)\s+(\S+)", block)
        require(len(names) == 1 and names[0] not in items, "unexpected declaration: " + str(path))
        items[names[0]] = block.strip()
    return items


def signature(declaration):
    body = re.split(r"(?m)^(?:def|axiom)\s+", declaration, maxsplit=1)[1].split(":=", 1)[0]
    name, body = body.split(maxsplit=1)
    domains = []
    binder = re.compile(r"^(?:\{([^:{}]+):([^{}]+)\}|\(([^:()]+):([^()]+)\))")
    while match := binder.match(body):
        implicit, implicit_type, explicit, explicit_type = match.groups()
        for _ in (implicit or explicit).split():
            domains.append((implicit is not None, "".join((implicit_type or explicit_type).split())))
        body = body[match.end():].lstrip()
    require(body.startswith(":"), "invalid callee telescope: " + name)
    *arrows, codomain = body[1:].split("→")
    domains.extend((False, "".join(arrow.split())) for arrow in arrows)
    return name, domains, "".join(codomain.split())


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    require(receipt["status"] == "checked_original_body_extracted" and
            receipt["source_commit"] == SOURCE_COMMIT and receipt["native_source_edited"] is False and
            receipt["aeneas_commit"] == AENEAS_COMMIT and receipt["charon_commit"] == CHARON_COMMIT and
            receipt["rust_toolchain"] == "nightly-2026-09-17" and receipt["target"] == TARGET and
            receipt["llbc_has_errors"] is False, "execution verify receipt provenance changed")
    artifacts = receipt["artifacts"]
    require(set(artifacts) == ARTIFACTS, "execution verify artifact set changed")
    for name, digest in artifacts.items():
        require(sha(root / EXTRACTION / name) == digest, "raw execution verify artifact differs: " + name)
    source_hashes = receipt["source_hashes"]
    require(set(source_hashes) == {span[0] for span in SOURCES.values()}, "source set changed")
    for name, digest in source_hashes.items():
        require(sha(root.parents[1] / name) == digest, "frozen execution verify source differs: " + name)
    commands = receipt["commands"]
    require([(item["name"], item["exit_code"]) for item in commands] == [("charon", 0), ("aeneas", 0)],
            "execution verify capture/replay outcome changed")
    capture, replay = [item["command"] for item in commands]
    baseline = json.loads((root / "extraction/reconstruction/receipt.json").read_text())
    fingerprints = baseline["tool_binary_sha256"]
    require({capture[0], replay[0]} <= fingerprints.keys() and
            receipt["tool_binary_sha256"] == {tool: fingerprints[tool] for tool in (capture[0], replay[0])} and
            Path(capture[0]).name == "charon" and Path(replay[0]).name == "main.exe" and
            capture[1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"] and
            capture[4].startswith("--dest-file=") and capture[4].removeprefix("--dest-file=") == replay[-1] and
            capture[5:12] == ["--start-from=" + STAGES, "--opaque=" + OPAQUE[0], "--include=" + INCLUDE,
                *["--opaque=" + name for name in OPAQUE[1:]]] and
            capture[12] == "--" and capture[13] == next(
                word for word in baseline["commands"][0]["command"] if word.startswith("--manifest-path=")) and
            capture[14:] == ["-p", "bulksketch", "--lib", "--locked", "--target", TARGET] and
            replay[1:-2] == ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
                "-print-error-emitters", "-split-files", "-dest"] and
            Path(replay[-2]).name == "Arithmetic" and Path(replay[-1]).name == "arithmetic.llbc",
            "execution verify capture or checked Lean command changed")
    require(receipt["environment"] == {
        "RUSTUP_TOOLCHAIN": "nightly-2026-09-17",
        "CARGO_TARGET_DIR": str(Path(replay[-1]).parent / "target"),
        "CARGO_BUILD_JOBS": "1",
        "CARGO_NET_OFFLINE": "true",
    }, "execution verify capture environment changed")

    llbc = json.loads((root / EXTRACTION / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    options = translated["options"]
    require(llbc["has_errors"] is False and options["start_from"] == [STAGES] and
            options["include"] == [INCLUDE] and options["opaque"] == OPAQUE and
            options["dest_file"] == replay[-1], "execution verify extraction selection changed")
    targets = translated["target_information"]
    require(len(targets) == 1 and targets[0]["key"] == TARGET and targets[0]["value"]["target_pointer_size"] == 8,
            "unexpected execution verify target")
    seen = set()
    for function in translated["fun_decls"]:
        if not function:
            continue
        meta = function["item_meta"]
        name = meta["name"][-1].get("Ident", [None])[0]
        if name not in SOURCES:
            continue
        span = meta["span"]["Untagged"]["data"]
        file = translated["files"][span["file_id"]]
        path, start, start_col, end, end_col = SOURCES[name]
        require(file["name"] == {"Local": path} and
                hashlib.sha256(file["contents"].encode()).hexdigest() == source_hashes[path] and
                span["beg"] == {"line": start, "col": start_col} and
                span["end"] == {"line": end, "col": end_col} and
                ("Structured" in function["body"] if name == "verify" else function["body"] == "Opaque") and
                name not in seen, "execution verify source span or opacity differs: " + name)
        seen.add(name)
    require(seen == SOURCES.keys(), "missing original source wrapper or callee")

    types = declarations(root / RAW / "Types.lean")
    for path, names in TYPE_DEPENDENCIES.items():
        shared = declarations(root / path)
        require(all(types[name] == shared[name] for name in names), "shared type differs: " + path)
    external = declarations(root / RAW / "FunsExternal_Template.lean")
    for name, path in CALLS.items():
        require(signature(external[name]) == signature(declarations(root / path)[name]),
                "checked callee signature differs: " + name)
    raw_path = RAW / "Funs.lean"
    original = declarations(root / raw_path)[NAME]
    require((root / ACTIVE).read_text() == HEADER + original + "\n\nend bulksketch\n",
            "compiled execution verify projection differs")
    return {
        "raw_generated_file": str(raw_path), "raw_file_sha256": sha(root / raw_path),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": 1,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + NAME], "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
