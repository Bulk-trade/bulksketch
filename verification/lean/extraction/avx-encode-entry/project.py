#!/usr/bin/env python3
"""Check three stock AVX captures and the exact native encoder projections."""
from hashlib import sha256
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/avx-encode-entry")
ACTIVE = Path("bridge/Arithmetic/AvxEncodeEntryGenerated.lean")
SINGLE = Path("bridge/Arithmetic/AvxSingletonGenerated.lean")
SOURCE = "src/backend/x86_vpclmul512.rs"
PREFIX = "bulksketch::backend::x86_vpclmul512::"
WRAPPER = "{impl bulksketch::backend::contract::BulkKernels for " + PREFIX + "Vpclmul512}::encode_nonzero"
WRAPPER_MARKER = "/-- [" + PREFIX + (
    "{impl bulksketch::backend::contract::BulkKernels<F> for "
    + PREFIX + "Vpclmul512}::encode_nonzero]"
)
FUNCTION = "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero"
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest"]
TARGETS = {
    "encode": ([WRAPPER], [WRAPPER], {"encode_nonzero": (144, 4, 158, 5)}),
    "insert-single-broadcast": (
        [PREFIX + "insert_single"], [PREFIX + "insert_single", PREFIX + "broadcast"],
        {"insert_single": (712, 0, 747, 1), "broadcast": (750, 0, 752, 1)},
    ),
    "insert-32": (
        [PREFIX + "insert_32"], [PREFIX + "insert_32"], {"insert_32": (616, 0, 705, 1)},
    ),
}
SHARED = {f"bridge/Arithmetic/{module}.lean" for module in (
    "AvxInsertDispatchGenerated", "PortableEncodingGenerated", "AvxEncode18Runtime", "AvxSliceKernelGenerated",
)}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def original(text, marker):
    return text[text.index(marker):text.rindex("end bulksketch")]


def check(root=ROOT, entry="encode"):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-linear-entry/receipt.json").read_text())
    require(all(receipt[key] == parent[key] for key in (
        "source_commit", "rust_toolchain", "target", "aeneas_commit", "charon_commit", "tool_binary_sha256",
    )) and receipt["native_source_edited"] is False, "AVX encode tool receipt differs")
    require(receipt["artifacts"] == ARTIFACTS and set(receipt["captures"]) == set(TARGETS),
            "AVX encode artifact receipt differs")
    for item, digest in ARTIFACTS.items():
        require(sha(root / DIRECTORY / item) == digest, "AVX encode capture artifact differs: " + str(DIRECTORY / item))
    require(set(receipt["source_sha256"]) == {SOURCE} and set(receipt["shared_sha256"]) == SHARED,
            "AVX encode source bindings incomplete")
    source_hash = receipt["source_sha256"][SOURCE]
    require(sha(root.parents[1] / SOURCE) == source_hash, "AVX encode Rust source differs")
    for item, digest in receipt["shared_sha256"].items():
        require(sha(root / item) == digest, "AVX encode shared binding differs: " + item)
    raw = {}
    for lane, (roots, includes, spans) in TARGETS.items():
        path = root / DIRECTORY / lane
        capture = json.loads((path / "arithmetic.llbc").read_text())
        crate = capture["translated"]
        opts = crate["options"]
        require(capture["has_errors"] is False and opts["skip_borrowck"] is False and
                opts["start_from"] == roots and opts["include"] == includes,
                "AVX encode capture options differ: " + lane)
        embedded = [file["contents"] for file in crate["files"] if file and file["name"] == {"Local": SOURCE}]
        require(len(embedded) == 1 and sha256(embedded[0].encode()).hexdigest() == source_hash,
                "AVX encode embedded Rust source differs: " + lane)
        methods = {}
        for fn in crate["fun_decls"]:
            if not fn or not isinstance(fn["body"], dict) or "Structured" not in fn["body"]:
                continue
            method = fn["item_meta"]["name"][-1].get("Ident", [""])[0]
            if method not in spans:
                continue
            location = fn["item_meta"]["span"]["Untagged"]["data"]
            if crate["files"][location["file_id"]]["name"] != {"Local": SOURCE}:
                continue
            methods[method] = (location["beg"]["line"], location["beg"]["col"],
                               location["end"]["line"], location["end"]["col"])
        require(methods == spans, "AVX encode structured source spans differ: " + lane)
        recorded = receipt["captures"][lane]
        ch, ae, replay = (recorded["commands"][key] for key in ("charon", "aeneas", "replay"))
        outputs = {file.name: sha(file) for file in sorted((path / "Arithmetic").glob("*.lean"))}
        require(ch["exit_code"] == ae["exit_code"] == replay["exit_code"] == 0 and
                ch["command"][4].removeprefix("--dest-file=") == ae["command"][-1] == replay["command"][-1] and
                ch["command"][-2:] == ["--target", receipt["target"]] and
                [arg.removeprefix("--start-from=") for arg in ch["command"] if arg.startswith("--start-from=")] == roots and
                [arg.removeprefix("--include=") for arg in ch["command"] if arg.startswith("--include=")] == includes and
                ae["command"][1:-2] == replay["command"][1:-2] == FLAGS and
                recorded["replay_outputs"] == outputs, "AVX encode checked replay differs: " + lane)
        raw[lane] = (path / "Arithmetic/Funs.lean").read_text()
    encode = original(raw["encode"], WRAPPER_MARKER)
    require(encode.count(WRAPPER_MARKER) == 7, "AVX encode original loop declarations differ")
    for n in range(3):
        name = f"{FUNCTION}_loop{n}.body"
        notation = f'local notation "{name}" => ({name} insertModel)\n\n'
        marker = f"{WRAPPER_MARKER}: loop {n}:"
        encode = encode.replace(marker, notation + marker, 1)
    aliases = "".join(f'local notation "{FUNCTION}_loop{n}" => ({FUNCTION}_loop{n} insertModel)\n'
                      for n in range(3))
    marker = WRAPPER_MARKER + ":\n"
    encode = encode.replace(marker, aliases + "\n" + marker, 1)
    require((root / ACTIVE).read_text() == ENCODE_HEADER + encode + "end bulksketch\n",
            "AVX encode entry projection differs")
    singleton = original(raw["insert-single-broadcast"], "/-- [" + PREFIX + "broadcast]")
    width32 = original(raw["insert-32"], "/-- [" + PREFIX + "insert_32]")
    require((root / SINGLE).read_text() == SINGLE_HEADER + singleton + width32 + "end bulksketch\n",
            "AVX singleton projection differs")
    require(entry in {"encode", "singleton"}, "unknown AVX encode projection")
    raw_path = DIRECTORY / ("encode" if entry == "encode" else "insert-single-broadcast") / "Arithmetic/Funs.lean"
    active = ACTIVE if entry == "encode" else SINGLE
    return {"raw_generated_file": str(raw_path), "raw_file_sha256": sha(root / raw_path),
            "compiled_projection": str(active), "projection_file_sha256": sha(root / active),
            "source_declarations_retained_verbatim": 7 if entry == "encode" else 3,
            "native_source_edited": False, "shared_types_and_function_dictionary_declarations_checked": True}


ENCODE_HEADER = '-- Checked original AVX encoder and three emitted singleton loop bodies.\nimport Arithmetic.AvxInsertDispatchGenerated\nimport Arithmetic.PortableEncodingGenerated\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.dupNamespace false\nset_option linter.unusedVariables false\n\nnamespace bulksketch\n\nvariable (encode18Model : AvxInsertDispatchRuntime.Batch)\nvariable (insertModel : {F : Type} → field.BinaryField F → AvxInsertDispatchRuntime.Batch)\n\nlocal notation "backend.x86_vpclmul512.encode_18" => encode18Model\nlocal notation "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero" => insertModel\n\n'
SINGLE_HEADER = '-- Original checked singleton entry points, with scoped register and memory bindings.\nimport Arithmetic.AvxEncode18Runtime\nimport Arithmetic.AvxSliceKernelGenerated\n\nopen Aeneas Aeneas.Std Result Error\nset_option linter.dupNamespace false\nset_option linter.unusedVariables false\n\nnamespace bulksketch\n\nvariable (baseModel : AvxEncode18Runtime.Bases) (loadModel : AvxSquareRuntime.Load)\nvariable (storeModel : AvxSquareRuntime.Store)\n\nlocal notation "core.core_arch.x86.__m512i" => Avx512Register.Word512\nlocal notation "core.num.U64.to_ne_bytes" => X86PclmulRuntime.unsignedBytes\nlocal notation "core.num.I64.from_ne_bytes" => X86PclmulRuntime.signedFromBytes\nlocal notation "core.core_arch.x86.avx512f._mm512_set1_epi64" => Avx512Register.broadcast\nlocal notation "core.core_arch.x86.avx512f._mm512_set_epi64" => AvxEncode18Runtime.set8\nlocal notation "core.core_arch.x86.avx512f._mm512_permutexvar_epi64" => AvxEncode18Runtime.permute\nlocal notation "core.core_arch.x86.avx512f._mm512_permutex2var_epi64" => AvxEncode18Runtime.permuteTwo\nlocal notation "core.core_arch.x86.avx512f._mm512_mask_mov_epi64" => AvxEncode18Runtime.maskMove\nlocal notation "core.core_arch.x86.avx512f._mm512_unpacklo_epi64" => (Avx512Register.unpack false)\nlocal notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords\nlocal notation "backend.x86_vpclmul512.single_bases" => baseModel\nlocal notation "backend.x86_vpclmul512.load" => loadModel\nlocal notation "backend.x86_vpclmul512.store" => storeModel\nlocal notation "backend.x86_vpclmul512.update_single_block" =>\n  (backend.x86_vpclmul512.update_single_block loadModel storeModel)\n\n'
ARTIFACTS = {'encode/arithmetic.llbc': '17a85687a9fbe764127f5e88686709e399daf6aa3bcf348ba6c5ead4a317bb0f',
 'encode/charon.log': '617f81aff2fe80ad443edb83a40a9539b4f2b2259daec88e87783e5bd2dc797b',
 'encode/aeneas.log': '1e9fb1bd4e14881e7bbcd1ff728d9eb05288bdd93738c51baf740a23f175c9a2',
 'encode/replay.log': '40d1aa699b7e62bcfea747d1d292ede9e65f0a04f59edf827bae1a2ee77741ea',
 'encode/Arithmetic/Funs.lean': '4be01e703bacd3e785f9aee162b61645bffe6d8db454aa7ee243a1e87c0f6527',
 'encode/Arithmetic/FunsExternal_Template.lean': '31435511f1289e3b2a90a5fb3dba72c29f9a54cdf31b22d8ac09b15d8c988183',
 'encode/Arithmetic/Types.lean': '21a2271bf5a1071312f0cfd02b0cf7db0d202e6a6e9f64a75836a019207b1fef',
 'insert-single-broadcast/arithmetic.llbc': '747b70a1e219625760e16ba07d64ca4202103be9f8750b2c6d2c2cfd1de45aa7',
 'insert-single-broadcast/charon.log': '68fedb2f16a0db85147eb4e5fbde05813eff06c2dd6e7f1014c08ff28f5eb9ad',
 'insert-single-broadcast/aeneas.log': '0819f515f6fb779e609dff01edc03f75f82d6fb30c07e0bf57b10d6f58e5c935',
 'insert-single-broadcast/replay.log': '594fb9b4d848cd7cdc472814451438e7ad9484ab97d5a788881797f435491fca',
 'insert-single-broadcast/Arithmetic/Funs.lean': 'e71a439c0691aacb322a7335ea2a15ece631a30586eea58a08641706e7d30611',
 'insert-single-broadcast/Arithmetic/FunsExternal_Template.lean': '7869ef2832638bc350eca9b27f5a5993c627841f0e678b7a12667f44343e841c',
 'insert-single-broadcast/Arithmetic/Types.lean': '9b78171eea85335494bba82fe6d25cc00734536d5fdd57b0c745df091935998f',
 'insert-single-broadcast/Arithmetic/TypesExternal_Template.lean': 'e059007c1981aacd1410896cef572b2f58252192d0659b05a45707715b1cc99e',
 'insert-32/arithmetic.llbc': '6aa7fdf3e6b6c5361d744e724db73d5bf4de9d4805bfff414ca2b93e90aa5ed1',
 'insert-32/charon.log': 'e1f6c4de1c367416b711d8e317a2c89b79a5355f0c787dc6b6ff8980357a71ec',
 'insert-32/aeneas.log': 'f3fbe3ad358f1e792692aa4bb869480ac1702405f76a834489f826fd47ae0f31',
 'insert-32/replay.log': '54a65454452dfcf5aacecac9531ed2d841fc1f463a277aa15fb079fa1aa7f69f',
 'insert-32/Arithmetic/Funs.lean': 'd4fedfb6db7353d4e81c027e39d09bafe8200c9b3729d6e843b2245151d342c4',
 'insert-32/Arithmetic/FunsExternal_Template.lean': 'bd5c1c2bb7631a69c3e7b60b4200bae134358d829f96d6285d6dfdc4883655e0',
 'insert-32/Arithmetic/Types.lean': '9b78171eea85335494bba82fe6d25cc00734536d5fdd57b0c745df091935998f',
 'insert-32/Arithmetic/TypesExternal_Template.lean': 'e059007c1981aacd1410896cef572b2f58252192d0659b05a45707715b1cc99e'}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--entry", choices=("encode", "singleton"), default="encode")
    print(json.dumps(check(entry=parser.parse_args().entry), indent=2))
