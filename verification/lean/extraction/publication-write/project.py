#!/usr/bin/env python3
"""Check the original Publication::write extraction, controls and active projection."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/publication-write")
ACTIVE = Path("bridge/Arithmetic/PublicationWriteGenerated.lean")
SOURCE = "src/sketch/api.rs"
LLBC_SHA = "f867db8bb92a6085249b9ffe8fa0a2ef5a6eb93bcda575dcae665e8765b947c0"
PATCH_SHA = "d3674c545b1960ff86c0a738254e072085656f1369680eb286173105ccca979c"
RAW_SHA = "eaa265277ccf2d24946d463f800a38d6327b703a1ca5c3fcb72b9ebbfc141a1b"
ACTIVE_SHA = "f53dd46ec6bd2f53e3429ea0dbaff7f91f06b33aa957aca075b831f4c910dab8"
OPTIONS = {'start_from': ['bulksketch::sketch::api::_::write'], 'include': ['bulksketch::sketch::api::_::write'], 'opaque': ['bulksketch::sketch::api::_::new', 'bulksketch::sketch::api::_::fail', 'bulksketch::sketch::api::_::finish']}
FLAGS = ["-backend", "lean", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files"]

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["variant_id"] == "checked-publication-write-branches-v1"
            and receipt["source_commit"] == "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
            and receipt["charon_commit"] == "7b462d9159db2ed3015162352183906a30bfafc6"
            and receipt["aeneas_commit"] == "ab34bd28458a08c150b7cbf1873e59af74588138"
            and receipt["target"] == "x86_64-apple-darwin" and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["native_source_edited"] is False and receipt["native_llbc_edited"] is False
            and receipt["mandatory_checks"] is True and receipt["variant_patch_sha256"] == PATCH_SHA,
            "invalid publication write checked receipt")
    for name, digest in receipt["artifacts"].items():
        require(sha(root / name) == digest, "publication write captured artifact differs: " + name)
    for name, digest in receipt["runtime_sha256"].items():
        require(sha(root / name) == digest, "publication write scoped runtime differs: " + name)
    llbc_path = root / DIRECTORY / "arithmetic.llbc"
    require(sha(llbc_path) == LLBC_SHA and sha(root / receipt["variant_patch"]) == PATCH_SHA,
            "publication write original capture or compiler patch differs")
    capture = json.loads(llbc_path.read_bytes())
    crate = capture["translated"]
    options = crate["options"]
    require(capture["has_errors"] is False and options["skip_borrowck"] is False
            and all(options[key] == value for key, value in OPTIONS.items()),
            "publication write frozen capture scope differs")
    source = root.parents[1] / SOURCE
    files = [item for item in crate["files"] if item and item["name"] == {"Local": SOURCE}]
    require(len(files) == 1 and files[0]["contents"].encode() == source.read_bytes()
            and receipt["source_sha256"] == {SOURCE: sha(source)},
            "publication write frozen Rust source differs")
    declaration, = [f for f in crate["fun_decls"] if f and
                    f["item_meta"]["name"][-1].get("Ident", [""])[0] == "write"]
    data = declaration["item_meta"]["span"]["Untagged"]["data"]
    require(data == {"file_id": files[0]["id"], "beg": {"line": 262, "col": 4},
                     "end": {"line": 312, "col": 5}}, "publication write original span differs")
    ch = receipt["charon_command"]
    require(ch[1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"]
            and ch[-7:] == ["-p", "bulksketch", "--lib", "--locked", "--offline", "--target", "x86_64-apple-darwin"],
            "publication write original capture command differs")
    controls = json.loads((root / DIRECTORY / "controls.json").read_text())
    require(controls["status"] == "passed" and controls["compiler_binary_sha256"] == receipt["patched_binary_sha256"],
            "publication write checked compiler differs")
    expected = {"checked": 0, "strict": 0, "stock": 1, "disabled": 1,
                "unchecked": 1, "wrong-metadata": 1, "unrelated-frame": 0}
    require({name: entry["exit_code"] for name, entry in controls["runs"].items()} == expected,
            "publication write replay control exits differ")
    for name, entry in controls["runs"].items():
        command = entry["command"]
        log = root / DIRECTORY / (name + ".log")
        require(command[3:3+len(FLAGS)] == FLAGS
                and ("-checks" in command) == (name != "unchecked")
                and ("-strict-joins" in command) == (name in {"strict", "wrong-metadata"})
                and ("BULKSKETCH_PUBLICATION_WRITE_JOIN=0" in command) == (name == "disabled")
                and sha(log) == entry["log_sha256"], "publication write replay control differs: " + name)
        if entry["diagnostic"]:
            require(entry["diagnostic"] in log.read_text(), "publication write rejection differs: " + name)
        if name not in {"wrong-metadata", "unrelated-frame"}:
            require(entry["input_sha256"] == LLBC_SHA, "publication write original replay input differs")
    body = declaration["body"]["Structured"]
    changed = []
    def mutate(node):
        if isinstance(node, dict):
            if node.get("id") == 949 and set(node) >= {"kind", "span"} and "Assign" in node["kind"]:
                destination = node["kind"]["Assign"][0]
                require(destination["kind"] == {"Local": 66}, "publication write mutation target differs")
                destination["kind"] = {"Local": 62}
                changed.append(949)
            for child in node.values():
                mutate(child)
        elif isinstance(node, list):
            for child in node:
                mutate(child)
    mutate(body)
    wrong = hashlib.sha256(json.dumps(capture).encode()).hexdigest()
    require(changed == [949] and controls["runs"]["wrong-metadata"]["input_sha256"] == wrong != LLBC_SHA,
            "publication write wrong metadata control differs")
    frame = root / "extraction/publication-frame"
    unrelated = controls["runs"]["unrelated-frame"]
    require(unrelated["input_sha256"] == sha(frame / "arithmetic.llbc")
            and unrelated["output_sha256"] ==
              {path.name: sha(path) for path in (frame / "Arithmetic").glob("*.lean")},
            "publication write unrelated frame replay differs")
    generated = root / DIRECTORY / "Arithmetic"
    hashes = {path.name: sha(path) for path in generated.glob("*.lean")}
    require(controls["runs"]["strict"]["output_sha256"] == controls["runs"]["checked"]["output_sha256"] == hashes,
            "publication write strict replay outputs differ")
    raw = generated / "Funs.lean"
    active = root / ACTIVE
    require(sha(raw) == RAW_SHA and sha(active) == ACTIVE_SHA, "publication write compiled projection differs")
    raw_types = (generated / "Types.lean").read_text()
    raw_functions = raw.read_text()
    name = "bulksketch::sketch::api::{bulksketch::sketch::api::Publication<'s>}::write"
    type_marker = "/-- [bulksketch::sketch::api::DecodeOutcome]"
    outcome = raw_types[raw_types.index(type_marker):raw_types.index("/-- [bulksketch::sketch::api::OutcomeStatus]")]
    closure = raw_types[raw_types.index("/-- [" + name + "::{closure}]"):raw_types.rindex("end bulksketch")]
    functions = raw_functions[raw_functions.index("/-- [" + name + "::{impl core::ops::function::FnOnce<(usize,)"):]
    projected = active.read_text()
    require(projected[projected.index(type_marker):] == outcome + closure + functions,
            "publication write checked declarations are not verbatim")
    declarations = re.findall(r"(?m)^(?:def|inductive)\s+(sketch\.api\.[^\s]+)", outcome + closure + functions)
    require(len(declarations) == len(set(declarations)) == 10
            and "sketch.api.Publication.write" in declarations, "publication write declaration inventory differs")
    return {"raw_generated_file": str(DIRECTORY / "Arithmetic/Funs.lean"),
            "raw_file_sha256": RAW_SHA, "compiled_projection": str(ACTIVE),
            "projection_file_sha256": ACTIVE_SHA, "source_declarations_retained_verbatim": len(declarations),
            "generated_declarations": ["bulksketch." + name for name in declarations],
            "native_source_edited": False, "native_llbc_edited": False,
            "shared_types_and_function_dictionary_declarations_checked": True,
            "translator_variant": receipt["variant_id"]}

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
