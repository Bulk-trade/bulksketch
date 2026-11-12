#!/usr/bin/env python3
"""Verify the original candidate scan and its stock Dense dispatch projection."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/candidates")
VARIANT = "checked-candidates-nested-return-v1"
SOURCE = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
AENEAS = "ab34bd28458a08c150b7cbf1873e59af74588138"
CHARON = "7b462d9159db2ed3015162352183906a30bfafc6"
TARGET = "x86_64-apple-darwin"
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest"]
CAPTURE = "bed7f690825a7843ec12634a23b4bcc4ed43ac7ef8fc6ac3296e4dc233273280"
DENSE_CAPTURE = "6abc0c02483645b0ba09bba7fb3cd02d9fc732e81009dfa9c8848afcec3400cf"
PATCH = DIRECTORY / "checked-candidates-nested-return.patch"
PATCH_HASH = "cd1cdc2ca14ef3657fb566dab0f6cf338de15bccd1c7ef81faf421a9cbaf34a5"
PATCHED_BINARY = "c1a66692bb841c3e5ec682bfba916c24c19767d536a63d240a9ba05444071fcc"
NATIVE = "decode.stages.Execution.candidates"
DENSE = "poly.Dense.Insts.BulksketchPolyPolynomial.eval_many_into"
MODES = {
    "inner": ("CandidateInnerGenerated", DIRECTORY, (NATIVE + "_loop0_loop0.body", NATIVE + "_loop0_loop0")),
    "outer": ("CandidateOuterGenerated", DIRECTORY, (NATIVE + "_loop0.body", NATIVE + "_loop0", NATIVE)),
    "dense": ("CandidateDenseEvalGenerated", DIRECTORY / "dense-eval", (DENSE,)),
}
SHARED_TYPES = {
    "ReconstructionTypes.lean": ("decode.stages.Execution", "decode.row.RowInput",
                                 "decode.scratch.RowWorkspace", "decode.roots.Roots",
                                 "types.DecodeFailure", "types.Stage"),
    "SliceKernelTypes.lean": ("backend.contract.BulkKernels",),
    "WorkScheduleGenerated.lean": ("decode.work.Charge",),
}
CONTROLS = {
    "checked": 0, "stock": 1, "unchecked": 1, "wrong-name": 1, "wrong-span": 1,
    "wrong-zip-cleanup": 1, "wrong-chunks-cleanup": 1, "wrong-constructor": 1,
    "wrong-return-id": 1, "wrong-normal-break": 1,
}
FILES = {
    "Arithmetic/Funs.lean", "Arithmetic/FunsExternal_Template.lean", "Arithmetic/Types.lean",
    "Arithmetic/TypesExternal_Template.lean", "arithmetic.llbc", "charon.log", "replay.log",
    "fresh-build.log", "checked-candidates-nested-return.patch", "controls.json",
    "dense-eval/arithmetic.llbc", "dense-eval/charon.log", "dense-eval/aeneas.log",
    "dense-eval/Arithmetic/Funs.lean", "dense-eval/Arithmetic/Types.lean",
    "dense-eval/Arithmetic/FunsExternal_Template.lean", "splitter-stock.log", "splitter-variant.log",
    *(name + ".log" for name in CONTROLS),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def declarations(path):
    text = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    result = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", text):
        names = re.findall(r"(?m)^(?:def|impl_def|structure|inductive|abbrev)\s+(\S+)", block)
        require(len(names) == 1 and names[0] not in result, "invalid candidate declaration block: " + str(path))
        result[names[0]] = block.strip()
    return result


def embedded_sources(path, expected):
    translated = json.loads(path.read_bytes())["translated"]
    for source, digest in expected.items():
        values = [item["contents"] for item in translated["files"] if item and item["name"] == {"Local": source}]
        require(len(values) == 1 and sha256(values[0].encode()).hexdigest() == digest,
                "candidate embedded Rust source differs: " + source)


def check(root=ROOT, kind="outer"):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["variant_id"] == VARIANT and receipt["source_commit"] == SOURCE
            and receipt["aeneas_commit"] == AENEAS and receipt["charon_commit"] == CHARON
            and receipt["target"] == TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["native_source_edited"] is False and receipt["native_llbc_edited"] is False
            and receipt["variant_patch"] == str(PATCH) and receipt["variant_patch_sha256"] == PATCH_HASH
            and receipt["patched_binary_sha256"] == PATCHED_BINARY, "candidate variant receipt differs")
    artifacts = receipt["files_sha256"]
    require(set(artifacts) == {str(DIRECTORY / name) for name in FILES}, "candidate artifact list differs")
    for path, digest in artifacts.items():
        require(sha(root / path) == digest, "candidate artifact differs: " + path)
    native_capture = root / DIRECTORY / "arithmetic.llbc"
    dense_capture = root / DIRECTORY / "dense-eval/arithmetic.llbc"
    require(sha(native_capture) == CAPTURE and sha(dense_capture) == DENSE_CAPTURE and sha(root / PATCH) == PATCH_HASH,
            "candidate pinned input differs")
    embedded_sources(native_capture, receipt["candidate_sources"])
    embedded_sources(dense_capture, receipt["dense_sources"])
    require(receipt["candidate_sources"] == CANDIDATE_SOURCES and receipt["dense_sources"] == DENSE_SOURCES,
            "candidate Rust source digest set differs")
    dense = receipt["dense_capture"]
    build = receipt["fresh_build"]
    require(build["exit_code"] == 0 and build["command"][-2:] == ["-j", "2"]
            and build["command"][-4] == "--root", "candidate variant build receipt differs")
    patched = str(Path(build["command"][-3]) / "_build/default/main.exe")
    require(dense["sha256"] == DENSE_CAPTURE and dense["exit_code"] == 0
            and dense["aeneas_sha256"] == STOCK_AENEAS and dense["command"][1:-2] == FLAGS
            and dense["command"][-1].endswith("/dense-eval/arithmetic.llbc")
            and dense["charon_command"][5] ==
                "--start-from={impl bulksketch::poly::Polynomial for bulksketch::poly::Dense}::eval_many_into"
            and "Generated:" in (root / DIRECTORY / "dense-eval/aeneas.log").read_text(),
            "stock Dense candidate evaluation capture differs")
    native = receipt["candidate_capture"]
    require(native["sha256"] == CAPTURE and native["charon_exit"] == 0
            and native["charon_command"][5:10] == [
                "--start-from=bulksketch::decode::stages", "--opaque=bulksketch::decode::stages::_::_",
                "--include=bulksketch::decode::stages::_::candidates",
                "--opaque=bulksketch::decode::stages::check_workspace",
                "--opaque=bulksketch::poly::dense::_::eval_many_into",
            ], "original candidate capture command differs")
    controls = json.loads((root / DIRECTORY / "controls.json").read_text())
    require(controls["original_sha256"] == CAPTURE and controls["variant_sha256"] == PATCHED_BINARY
            and set(controls["controls"]) == set(CONTROLS), "candidate controls receipt differs")
    for name, status in CONTROLS.items():
        row = controls["controls"][name]
        log = root / DIRECTORY / (name + ".log")
        expected_flags = [flag for flag in FLAGS if flag != "-checks" or name != "unchecked"]
        require(row["status"] == status and row["command"][1:-2] == expected_flags
                and row["command"][0] == (dense["command"][0] if name == "stock" else patched)
                and row["log_sha256"] == sha(log), "candidate control command or log differs: " + name)
        if status:
            text = log.read_text()
            require("Returns inside of nested loops are not supported yet" in text
                    and "PrePasses.ml, line 647" in text and "src/decode/stages.rs" in text,
                    "candidate rejection differs: " + name)
    require(controls["unchanged_splitter"]["files"] == SPLITTER_FILES
            and all("Generated:" in (root / DIRECTORY / (name + ".log")).read_text()
                    for name in ("splitter-stock", "splitter-variant")),
            "unrelated splitter compatibility control differs")
    for path, digest in RUNTIME_HASHES.items():
        require(sha(root / path) == digest, "candidate scoped runtime differs: " + path)
    native_types = declarations(root / DIRECTORY / "Arithmetic/Types.lean")
    for filename, names in SHARED_TYPES.items():
        active_types = declarations(root / "bridge/Arithmetic" / filename)
        require(all(native_types[name] == active_types[name] for name in names),
                "candidate shared type differs: " + filename)
    dense_types = declarations(root / DIRECTORY / "dense-eval/Arithmetic/Types.lean")
    require(dense_types["backend.contract.BulkKernels"] == native_types["backend.contract.BulkKernels"],
            "stock Dense candidate dictionary differs")
    module, directory, names = MODES[kind]
    raw = directory / "Arithmetic/Funs.lean"
    active = Path("bridge/Arithmetic") / (module + ".lean")
    expected_raw = ("0e069920da3d4289674076d8af74f6464569705847f1d46c5b79a4346b6eebf0" if kind == "dense"
                    else "de5ed3d1c89bf45d995de0824ab40f7206792bd7297dd870c2629cc82cb7e461")
    require(sha(root / raw) == expected_raw, "pinned candidate generated body differs: " + str(raw))
    actual = declarations(root / active)
    original = declarations(root / raw)
    text = (root / active).read_text()
    header = text.split("/-- [", 1)[0]
    require(list(actual) == list(names) and all(actual[name] == original[name] and "sorry" not in actual[name]
            for name in names) and sha256(header.encode()).hexdigest() == HEADERS[kind],
            "compiled candidate projection differs")
    output = {
        "raw_generated_file": str(raw), "raw_file_sha256": sha(root / raw),
        "compiled_projection": str(active), "projection_file_sha256": sha(root / active),
        "source_declarations_retained_verbatim": len(names),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in names],
        "native_source_edited": False,
    }
    if kind != "dense":
        output["translator_variant"] = VARIANT
    return output


CANDIDATE_SOURCES = {'src/backend/contract.rs': '4d05ce564edc408ba04f5a907b159ad91018ba8cfd93126e17913ed49f7e3d59',
 'src/decode/row.rs': 'bf5ae89114d3bab811f1e0ca3b370cd916803bddd178471b3167e81b432df7bc',
 'src/decode/scratch.rs': '97016cadabf021829b567ff1472a9f11136f54059d78e457d58896cc318e50f6',
 'src/decode/stages.rs': '93825fcb5054e98e9af060a81da72d4770c29354d79822ccfc949cc55f6e9b23',
 'src/poly/dense.rs': '13b360fba6387dda36a9655f3f67d01be6752e4ca6b7f8e1824e7333bf3da644',
 'src/types.rs': '5702a8552c1158cf69f2155d2484f246f87475dc6bef3ea734be52348acd940d'}

DENSE_SOURCES = {'src/backend/contract.rs': '4d05ce564edc408ba04f5a907b159ad91018ba8cfd93126e17913ed49f7e3d59',
 'src/poly/dense.rs': '13b360fba6387dda36a9655f3f67d01be6752e4ca6b7f8e1824e7333bf3da644',
 'src/poly/mod.rs': '93fcb671a61dce34848723a52bc0f49e2f8c440f918d748f4101956dbb11ac2e',
 'src/types.rs': '5702a8552c1158cf69f2155d2484f246f87475dc6bef3ea734be52348acd940d'}

RUNTIME_HASHES = {'bridge/Arithmetic/AvxHornerChunkRuntime.lean': '8b4b25334dd663935446930ae7de5d9f3a52252e7afe236ab431dd48608c41d2',
 'bridge/Arithmetic/MutableZipRuntime.lean': '683a48af92e8c4f992d4f0893ed18679122344714cdda9a2293c07029b85776d',
 'bridge/Arithmetic/RebuiltLfsrRuntime.lean': '6fdef76755089ae0966294b4ba4ea7138b86780136ecd5083920ba49a022f2a2'}

HEADERS = {'dense': 'e3b4521188b499c8de1302cb7bfd16f65df623dafb7b27ad0a404f55ae892ca5',
 'inner': '4cf8accd88314ab310b1a7ca7dab307787d2bfc559b55c842b7bc9d67963f9b7',
 'outer': '5c7e4ec894c0d41ca4baaed585b29baf6aa4df45beb0f769c1e02a67de8d90bd'}

SPLITTER_FILES = {'Funs.lean': '4a1e1a13827ea38655bd055b65e579e17052f91a8e92ea82a72bbddb6c6f876a',
 'FunsExternal_Template.lean': '4c59046b038ddb5906a108fac743d2bfdafa10499b04405679623a05e331ef6d',
 'Types.lean': 'c1c3706fc639ac3c460be5b0043a2b49afa6b36f37172c27e5aca26f08c59abb'}

STOCK_AENEAS = '91f5a2776a79e2923517a2c4807c9fc017e79f185ae490502247f16e2941e330'

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--kind", choices=MODES, default="outer")
    print(json.dumps(check(kind=parser.parse_args().kind), indent=2))
