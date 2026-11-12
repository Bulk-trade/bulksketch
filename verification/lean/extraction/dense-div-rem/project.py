#!/usr/bin/env python3
"""Check the exact, unoutlined Dense division extraction and replay receipt."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
COMMON = importlib.util.spec_from_file_location("root_setup", ROOT / "extraction/root-setup/project.py")
setup = importlib.util.module_from_spec(COMMON)
COMMON.loader.exec_module(setup)
require, sha, declarations = setup.require, setup.sha, setup.declarations

DIRECTORY = Path("extraction/dense-div-rem")
RAW = DIRECTORY / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/DenseDivRemGenerated.lean")
VARIANT = "checked-dense-div-rem-v1"
PATCH = DIRECTORY / "checked-dense-div-rem.patch"
CAPTURE = "3ed726444d0c56ab36971d160b772014b3525d8df33f1c7317b9495f7486dbd2"
PATCH_HASH = "fbd95eba7f138b61635809eca867eca417b782b4f8701b39ca4c8e9038e4069c"
NAME = "poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into"
MARKER = "/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop body 0:"
HEADER = "465b1da7f482dc7beebe4a052bd4217636effd5c380d34985d6a41bea192452e"
OUTPUTS = ("Funs.lean", "FunsExternal_Template.lean", "Types.lean")
SOURCE_HASHES = {
    "src/poly/dense.rs": "13b360fba6387dda36a9655f3f67d01be6752e4ca6b7f8e1824e7333bf3da644",
    "src/types.rs": "5702a8552c1158cf69f2155d2484f246f87475dc6bef3ea734be52348acd940d",
    "src/backend/contract.rs": "4d05ce564edc408ba04f5a907b159ad91018ba8cfd93126e17913ed49f7e3d59",
}
CONTROLS = {"stock": 1, "flag-disabled": 1, "unchecked": 1, "checked": 0, "xor-stock": 0, "xor-patched": 0}
GUARDS = {
    "wrong_owner": "Unexpected Dense division raw-init ownership graph",
    "region_alias": "Unexpected Dense division raw-init ownership graph",
    "wrong_terminal": "Unexpected Dense division terminal Zip provenance",
}
FLAGS = ["-backend", "lean", "-sequential", "-no-progress-bar", "-print-error-emitters", "-split-files"]
ARTIFACTS = {str(RAW / name) for name in OUTPUTS}
ARTIFACTS |= {str(DIRECTORY / name) for name in ("arithmetic.llbc", "charon.log", "replay.log")}
ARTIFACTS |= {str(DIRECTORY / (name + ".log")) for name in CONTROLS}
ARTIFACTS |= {str(DIRECTORY / (name + ".log")) for name in GUARDS}
ARTIFACTS |= {str(DIRECTORY / name) for name in ("fresh-build.log", "direct-negative-instrumentation.patch",
                                                "synthetic-wrong-owner.py")}


def local_span(crate, decl):
    span = decl["item_meta"]["span"]["Untagged"]["data"]
    source = crate["files"][span["file_id"]]
    return source, span["beg"]["line"], span["end"]["line"]


def short_name(decl):
    return decl["item_meta"]["name"][-1].get("Ident", [""])[0]


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["variant_id"] == VARIANT and receipt["source_commit"] == setup.SOURCE
            and receipt["aeneas_commit"] == setup.AENEAS and receipt["charon_commit"] == setup.CHARON
            and receipt["target"] == setup.TARGET and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["native_source_edited"] is False and receipt["native_llbc_edited"] is False
            and receipt["variant_patch"] == str(PATCH) and receipt["variant_patch_sha256"] == PATCH_HASH
            and sha(root / PATCH) == PATCH_HASH and receipt["source_sha256"] == SOURCE_HASHES
            and set(receipt["files_sha256"]) == ARTIFACTS,
            "invalid direct Dense division receipt")
    for path, digest in receipt["files_sha256"].items():
        require(sha(root / path) == digest, "direct Dense division artifact differs: " + path)
    require(sha(root / DIRECTORY / "arithmetic.llbc") == CAPTURE, "original Dense division LLBC differs")
    for source, digest in SOURCE_HASHES.items():
        require(sha(root.parents[1] / source) == digest, "original Dense division source differs: " + source)

    llbc = json.loads((root / DIRECTORY / "arithmetic.llbc").read_text())
    crate = llbc["translated"]
    for path, digest in SOURCE_HASHES.items():
        embedded = [file["contents"] for file in crate["files"] if file and file["name"] == {"Local": path}]
        require(len(embedded) == 1 and hashlib.sha256(embedded[0].encode()).hexdigest() == digest,
                "original embedded Dense division source differs: " + path)
    opts, targets = crate["options"], crate["target_information"]
    require(llbc["has_errors"] is False and opts["start_from"] == ["bulksketch::poly::dense"]
            and opts["opaque"] == ["bulksketch::poly::dense::_::_", "bulksketch::poly::dense::normalized_len"]
            and len(targets) == 1 and targets[0]["key"] == setup.TARGET
            and targets[0]["value"]["target_pointer_size"] == 8,
            "direct Dense division target or LLBC capture scope differs")
    for kind, name, path, lines in (
        ("fun_decls", "div_rem_into", "src/poly/dense.rs", (40, 96)),
        ("type_decls", "RawProduct", "src/types.rs", (267, 270)),
    ):
        found = [decl for decl in crate[kind] if decl and short_name(decl) == name
                 and local_span(crate, decl)[0]["name"] == {"Local": path}]
        structured = [decl for decl in found if kind != "fun_decls" or
                      (isinstance(decl["body"], dict) and "Structured" in decl["body"])]
        require(len(structured) == 1, "missing exact original declaration: " + name)
        decl = structured[0]
        source, first, last = local_span(crate, decl)
        require((first, last) == lines and hashlib.sha256(source["contents"].encode()).hexdigest() == SOURCE_HASHES[path],
                "direct Dense division source span or embedded source differs: " + name)
        if name == "RawProduct":
            fields = [(field["name"], field["ty"]) for field in decl["kind"]["Struct"]]
            u64 = {"Untagged": {"Scalar": {"Integer": {"Unsigned": "U64"}}}}
            require(not any(decl["generics"].values()) and fields == [("lo", u64), ("hi", u64)],
                    "RawProduct no longer has two loan-free words")

    controls = receipt["controls"]
    outputs = {name: sha(root / RAW / name) for name in OUTPUTS}
    require(set(controls) == set(CONTROLS), "incomplete direct Dense division controls")
    flag = {"BULKSKETCH_DENSE_DIVISION": "1"}
    for name, exit_code in CONTROLS.items():
        row = controls[name]
        command = row["command"]
        builtin = name in {"stock", "xor-stock"}
        xor = name.startswith("xor-")
        binary = setup.BINARY_SHA256["aeneas"] if builtin else receipt["patched_binary_sha256"]
        require(row["exit_code"] == exit_code and row["binary_sha256"] == binary
                and row["env"] == ({} if builtin or name == "flag-disabled" else flag)
                and row["input_sha256"] == (receipt["xor_sha256"] if xor else CAPTURE)
                and command[1:-3] == FLAGS + ([] if name == "unchecked" else ["-checks"])
                and command[-3] == "-dest" and command[-1] == (receipt["xor_input"] if xor else opts["dest_file"])
                and sha(root / DIRECTORY / (name + ".log")) == row["log_sha256"],
                "direct Dense division control differs: " + name)
    require(sha(root / "extraction/portable-xor/arithmetic.llbc") == receipt["xor_sha256"]
            and controls["xor-stock"]["files"] == controls["xor-patched"]["files"]
            and set(controls["xor-stock"]["files"]) == set(OUTPUTS)
            and controls["checked"]["files"] == outputs,
            "direct Dense division checked output or compatibility replay differs")
    replay = receipt["replay"]
    require(replay["exit_code"] == 0 and replay["input_sha256"] == CAPTURE and replay["env"] == flag
            and replay["command"][1:-3] == FLAGS + ["-checks"] and replay["command"][-3] == "-dest"
            and replay["command"][-1] == opts["dest_file"] and replay["files"] == outputs
            and replay["binary_sha256"] == receipt["patched_binary_sha256"] and replay["source_files_byte_identical"] == 108
            and replay["build_log_sha256"] == sha(root / DIRECTORY / "fresh-build.log")
            and replay["log_sha256"] == sha(root / DIRECTORY / "replay.log"),
            "fresh direct Dense division replay differs")
    guards = receipt["negative_controls"]
    require(set(guards) == set(GUARDS), "incomplete direct Dense division guard controls")
    for name, diagnostic in GUARDS.items():
        log = root / DIRECTORY / (name + ".log")
        row = guards[name]
        require(row["exit_code"] == 1 and row["reason"] == diagnostic
                and row["log_sha256"] == sha(log) and diagnostic in log.read_text(),
                "direct Dense division guard control differs: " + name)

    types = declarations(root / RAW / "Types.lean")
    for path, names in {
        "Types.lean": ("types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField"),
        "SliceKernelTypes.lean": ("backend.contract.Arithmetic", "backend.contract.BulkKernels"),
    }.items():
        imported = declarations(root / "bridge/Arithmetic" / path)
        require(all(types[name] == imported.get(name) for name in names),
                "direct Dense division shared type or dictionary differs: " + path)
    functions = declarations(root / RAW / "Funs.lean")
    names = [name for name in functions if name.startswith(NAME)]
    header, marker, body = (root / ACTIVE).read_text().partition(MARKER)
    require(len(names) == 15 and NAME in names and hashlib.sha256(header.encode()).hexdigest() == HEADER
            and marker + body == "\n\n".join(functions[name] for name in names) + "\n\nend bulksketch\n",
            "compiled direct Dense division projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(names),
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in names],
        "native_source_edited": False,
        "translator_variant": VARIANT,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
