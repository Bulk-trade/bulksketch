#!/usr/bin/env python3
"""Fail-closed source/capture/projection check for the original AVX tile."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/avx-tile")
ACTIVE = Path("bridge/Arithmetic/AvxTileGenerated.lean")
RUST = "src/backend/x86_vpclmul512.rs"
SELECTOR = "bulksketch::backend::x86_vpclmul512::insert_tile"
SOURCE_SHA = "7a9c29dff254508671aa4122b20644b21a9cfb40f86ba5eaadce02bf680475d4"
LLBC_SHA = "95ae6994b20a908deae62e078f580ee2578c3ebd75ad2e21a8766cbcd5d1725b"
FILES = {
    "Funs.lean": "bbe8a001870d9ed30f185f4178a5e03291b9a0c24ff23c546fadff48f43fea11",
    "FunsExternal_Template.lean": "bd8312ec5c1883541fad78c4beda96ff8a76186a16480624b0cbc04f92714bb4",
    "Types.lean": "df213ef1128f0f4786c753b6266296b2c19fd53131e50196f6a5ec93c4ee15a8",
    "TypesExternal_Template.lean": "327c9bcfa1e90e14a4a8eac9d523fffdabf78b8bb0f16dfef73e62fe4016b144",
}
PATCH = "checked-avx-tile-history.patch"
PATCH_SHA = "ad584bbf586616835c3b3c4ec9039d13d55a157f97fb7e99ef31563b44dce06f"
ACTIVE_SHA = "d5d9c84f8ace5e4e39791df0409b8d04227fa786822a498f42b98b8b30515fea"

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check_capture(source, llbc_path, generated, active, patch):
    require(sha(source) == SOURCE_SHA, "AVX tile original Rust source differs")
    require(sha(llbc_path) == LLBC_SHA, "AVX tile original LLBC differs")
    capture = json.loads(llbc_path.read_bytes())
    crate = capture["translated"]
    options = crate["options"]
    require(capture["has_errors"] is False and options["skip_borrowck"] is False
            and options["start_from"] == [SELECTOR]
            and options["opaque"] == [SELECTOR.rsplit("::", 1)[0] + suffix
                                      for suffix in ("::load", "::horizontal_xor")],
            "AVX tile frozen capture scope differs")
    files = [item for item in crate["files"] if item and item["name"] == {"Local": RUST}]
    require(len(files) == 1 and files[0]["contents"].encode() == source.read_bytes(),
            "AVX tile embedded Rust differs")
    declaration, = [item for item in crate["fun_decls"] if item and
                    "::".join(part.get("Ident", [""])[0] for part in item["item_meta"]["name"]) == SELECTOR]
    meta = declaration["item_meta"]["span"]["Untagged"]["data"]
    require(meta == {"file_id": files[0]["id"], "beg": {"line": 438, "col": 0},
                     "end": {"line": 459, "col": 1}}, "AVX tile source span differs")
    body = declaration["body"]["Structured"]
    loops = [stmt["id"] for stmt in body["body"]["statements"]
             if isinstance(stmt["kind"], dict) and "Loop" in stmt["kind"]]
    require(loops == [183, 508], "AVX tile original loop boundaries differ")
    for name, digest in FILES.items():
        require(sha(generated / name) == digest, "AVX tile original checked declaration drift: " + name)
    require(sha(patch) == PATCH_SHA, "AVX tile scoped compiler patch differs")
    require(sha(active) == ACTIVE_SHA, "AVX tile active projection differs")
    raw_funs = (generated / "Funs.lean").read_text()
    raw_types = (generated / "Types.lean").read_text()
    compiled = active.read_text()
    closure = raw_types[raw_types.index("/-- [bulksketch::backend::x86_vpclmul512::insert_tile::{closure}]"):
                        raw_types.rindex("end bulksketch")]
    tail = raw_funs[raw_funs.index("/-- [bulksketch::backend::x86_vpclmul512::insert_tile::{impl core::ops::function::FnMut"):]
    projection = re.sub(
        r'^local notation "backend\.x86_vpclmul512\.insert_tile_loop0(?:\.body)?" => [^\n]+\n\n',
        "", compiled[compiled.index(closure):], flags=re.M)
    require(projection == closure + tail, "AVX tile declarations are not verbatim")
    names = re.findall(r"(?m)^def\s+(backend\.x86_vpclmul512\.insert_tile\S*)", projection)
    require(len(names) == len(set(names)) == 12, "AVX tile original declaration count differs")
    return {"status": "passed", "raw_generated_file": str(generated / "Funs.lean"),
            "raw_file_sha256": FILES["Funs.lean"], "compiled_projection": str(active),
            "projection_file_sha256": ACTIVE_SHA, "source_declarations_retained_verbatim": len(names),
            "generated_declarations": ["bulksketch." + name for name in names],
            "checked_original_llbc_sha256": LLBC_SHA,
            "source_rust_sha256": SOURCE_SHA, "compiler_patch_sha256": PATCH_SHA,
            "native_source_edited": False, "native_llbc_edited": False,
            "shared_types_and_function_dictionary_declarations_checked": True,
            "translator_variant": "checked-avx-tile-history-v1"}

def check(root=ROOT, source=None):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["variant_id"] == "checked-avx-tile-history-v1"
            and receipt["source_commit"] == "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
            and receipt["charon_commit"] == "7b462d9159db2ed3015162352183906a30bfafc6"
            and receipt["aeneas_commit"] == "ab34bd28458a08c150b7cbf1873e59af74588138"
            and receipt["native_source_edited"] is False and receipt["native_llbc_edited"] is False
            and receipt["mandatory_checks"] is True and receipt["variant_patch_sha256"] == PATCH_SHA,
            "invalid checked AVX tile translator receipt")
    for name, digest in receipt["artifacts"].items():
        require(sha(root / name) == digest, "AVX tile captured artifact differs: " + name)
    for name, digest in receipt["runtime_sha256"].items():
        require(sha(root / name) == digest, "AVX tile scoped runtime differs: " + name)
    controls = json.loads((root / DIRECTORY / "controls.json").read_text())
    require(controls["status"] == "passed" and controls["checked_binary_sha256"] == receipt["patched_binary_sha256"],
            "AVX tile checked binary differs")
    expected = {"strict": 0, "checked": 0, "no-checks": 1, "disabled": 1, "wrong-site": 1,
                "unrelated-horizontal": 0, "unrelated-free-dispatch": 0,
                "unrelated-trait-dispatch": 0, "unrelated-insert18": 0}
    require({name: entry["exit_code"] for name, entry in controls["runs"].items()} == expected,
            "AVX tile scoped replay controls differ")
    for name, entry in controls["runs"].items():
        command = entry["command"]
        require(("-checks" in command) == (name != "no-checks")
                and ("-strict-joins" in command) == (name in {"strict", "wrong-site"})
                and ("BULKSKETCH_TILE_HISTORY=0" in command) == (name == "disabled")
                and sha(root / DIRECTORY / (name + ".log")) == entry["log_sha256"],
                "AVX tile control command or log differs: " + name)
        if entry["diagnostic"]:
            require(entry["diagnostic"] in (root / DIRECTORY / (name + ".log")).read_text(),
                    "AVX tile wrong rejection: " + name)
        if name in {"checked", "strict", "no-checks", "disabled"}:
            require(entry["input_sha256"] == LLBC_SHA, "AVX tile original input differs")
    require(controls["runs"]["strict"]["output_sha256"] == FILES
            and controls["runs"]["checked"]["output_sha256"] == FILES,
            "AVX tile checked replay outputs differ")
    wrong = json.loads((root / DIRECTORY / "arithmetic.llbc").read_bytes())
    declaration, = [item for item in wrong["translated"]["fun_decls"] if item and
                    item["item_meta"]["name"][-1].get("Ident", [""])[0] == "insert_tile"]
    local = declaration["body"]["Structured"]["locals"]["locals"][5]
    require(local["index"] == 5 and local["name"] == "steps", "AVX tile original steps local differs")
    local["name"] = "wrong_steps"
    wrong_digest = hashlib.sha256(json.dumps(wrong).encode()).hexdigest()
    require(controls["runs"]["wrong-site"]["input_sha256"] == wrong_digest != LLBC_SHA,
            "AVX tile wrong-site synthetic input differs")
    for name in ("horizontal", "free-dispatch", "trait-dispatch", "insert18"):
        parent = root / "extraction/avx-insert" / name
        row = controls["runs"]["unrelated-" + name]
        require(row["input_sha256"] == sha(parent / "arithmetic.llbc")
                and row["output_sha256"] ==
                {file: sha(parent / "Arithmetic" / file) for file in row["output_sha256"]},
                "AVX tile unrelated source replay differs: " + name)
    source = root.parents[1] / RUST if source is None else source
    result = check_capture(source, root / DIRECTORY / "arithmetic.llbc",
                           root / DIRECTORY / "Arithmetic", root / ACTIVE,
                           root / DIRECTORY / PATCH)
    result["raw_generated_file"] = str(DIRECTORY / "Arithmetic/Funs.lean")
    result["compiled_projection"] = str(ACTIVE)
    return result

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
