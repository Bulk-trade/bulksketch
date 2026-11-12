#!/usr/bin/env python3
"""Check exact stock AVX slice declarations and their scoped runtime bindings."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/avx-slice-kernel")
ACTIVE = Path("bridge/Arithmetic/AvxSliceKernelGenerated.lean")
SOURCE = "src/backend/x86_vpclmul512.rs"
SOURCE_COMMIT = "0a5bda53f6b07fcae8acd870e2d0c4a246d207e6"
ACTIVE_SHA = "f15095f5796769df16f5bbc26128e77f67dc4f1948b3aa921e1982ca57f6e041"
LLBC_SHA = "e8a0c2f73e812bcbc39755eabbe17bcea8beeefafb6d1436d4f2203b3392006c"
RAW_SHA = "de438394f3ff4818036b6dc2c927e648983db5902826269e8aedd873f60a87db"
MARKER = "/-- [bulksketch::backend::x86_vpclmul512::scale_kernel]: loop body"
DECLARATIONS = ['backend.x86_vpclmul512.scale_kernel_loop.body', 'backend.x86_vpclmul512.scale_kernel_loop', 'backend.x86_vpclmul512.scale_kernel', 'backend.x86_vpclmul512.square_kernel_loop.body', 'backend.x86_vpclmul512.square_kernel_loop', 'backend.x86_vpclmul512.square_kernel', 'backend.x86_vpclmul512.update_single_block']
SELECTORS = ['bulksketch::backend::x86_vpclmul512::update_single_block', 'bulksketch::backend::x86_vpclmul512::scale_kernel', 'bulksketch::backend::x86_vpclmul512::square_kernel']
INCLUDE = []
OPAQUE = ['bulksketch::backend::x86_vpclmul512::load', 'bulksketch::backend::x86_vpclmul512::store', 'bulksketch::backend::x86_vpclmul512::multiply', 'bulksketch::backend::x86_vpclmul512::xor_assign']
FLAGS = ['-backend', 'lean', '-checks', '-sequential', '-no-progress-bar', '-print-error-emitters', '-split-files', '-dest']

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["source_commit"] == SOURCE_COMMIT
            and receipt["charon_commit"] == "7b462d9159db2ed3015162352183906a30bfafc6"
            and receipt["aeneas_commit"] == "ab34bd28458a08c150b7cbf1873e59af74588138"
            and receipt["target"] == "x86_64-apple-darwin" and receipt["rust_toolchain"] == "nightly-2026-09-17"
            and receipt["native_source_edited"] is False and receipt["native_llbc_edited"] is False,
            "invalid stock AVX slice receipt")
    for name, digest in receipt["artifacts"].items():
        require(sha(root / name) == digest, "AVX slice captured artifact differs: " + name)
    for name, digest in receipt["runtime_sha256"].items():
        require(sha(root / name) == digest, "AVX slice scoped runtime differs: " + name)
    llbc_path = root / DIRECTORY / "arithmetic.llbc"
    require(sha(llbc_path) == LLBC_SHA, "AVX slice original LLBC differs")
    capture = json.loads(llbc_path.read_bytes())
    crate = capture["translated"]
    options = crate["options"]
    require(capture["has_errors"] is False and options["skip_borrowck"] is False
            and options["start_from"] == SELECTORS and options["include"] == INCLUDE
            and options["opaque"] == OPAQUE, "AVX slice capture scope differs")
    source = root.parents[1] / SOURCE
    files = [item for item in crate["files"] if item and item["name"] == {"Local": SOURCE}]
    require(len(files) == 1 and files[0]["contents"].encode() == source.read_bytes()
            and receipt["source_sha256"] == {SOURCE: sha(source)}, "AVX slice frozen Rust source differs")
    commands = receipt["commands"]
    ch, ae, replay = commands["charon"], commands["aeneas"], receipt["replay"]
    require(ch["exit_code"] == ae["exit_code"] == replay["exit_code"] == 0
            and ch["command"][1:4] == ["cargo", "--preset=aeneas", "--sysroot=default"]
            and ch["command"][-6:] == ["-p", "bulksketch", "--lib", "--locked", "--offline", "--target", "x86_64-apple-darwin"][-6:]
            and ae["command"][1:-2] == replay["command"][1:-2] == FLAGS
            and ch["command"][4].removeprefix("--dest-file=") == ae["command"][-1] == replay["command"][-1],
            "AVX slice checked commands differ")
    generated = root / DIRECTORY / "Arithmetic"
    require(replay["output_sha256"] == {path.name: sha(path) for path in generated.glob("*.lean")},
            "AVX slice stock replay differs")
    raw_path = generated / "Funs.lean"
    active_path = root / ACTIVE
    require(sha(raw_path) == RAW_SHA and sha(active_path) == ACTIVE_SHA,
            "AVX slice compiled projection differs")
    raw_text = raw_path.read_text()
    active_text = active_path.read_text()
    require(raw_text.count(MARKER) == active_text.count(MARKER) == 1,
            "AVX slice projection marker differs")
    compiled = re.sub(r'^local notation "backend\.x86_vpclmul512\.[^"]+" => [^\n]+\n\n',
                      "", active_text[active_text.index(MARKER):], flags=re.M)
    require(compiled == raw_text[raw_text.index(MARKER):],
            "AVX slice checked declarations are not verbatim")
    names = re.findall(r"(?m)^def\s+(backend\.x86_vpclmul512\.[^\s]+)", compiled)
    require(names == DECLARATIONS, "AVX slice source declaration inventory differs")
    return {"raw_generated_file": str(DIRECTORY / "Arithmetic/Funs.lean"),
            "raw_file_sha256": RAW_SHA, "compiled_projection": str(ACTIVE),
            "projection_file_sha256": ACTIVE_SHA,
            "source_declarations_retained_verbatim": len(names),
            "generated_declarations": ["bulksketch." + name for name in names],
            "native_source_edited": False,
            "shared_types_and_function_dictionary_declarations_checked": True}

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
