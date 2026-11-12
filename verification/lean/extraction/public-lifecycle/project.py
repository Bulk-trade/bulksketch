#!/usr/bin/env python3
"""Verify the original tiny probe and checked public result dispatch."""
from hashlib import sha256
import argparse
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/public-lifecycle")
TINY = Path("bridge/Arithmetic/TinyProbeGenerated.lean")
COMPLETED = Path("bridge/Arithmetic/DispatchCompletedGenerated.lean")
PATCH = "completed/checked-dispatch-result.patch"
PATCH_SHA = "bb8a1b98d1f263072d61379f471bd94e8a774e78d359022aa0aa3a03bf95518c"
BASE_BINARY = "91f5a2776a79e2923517a2c4807c9fc017e79f185ae490502247f16e2941e330"
PATCHED_BINARY = "26cd97c818e3e14b24cae92ca16b775a77f3ef7a76aa5d4fcba5caa06ef2c872"
PATCHED_SOURCE = "925aef4d27b367245a252818ab249f0d394885426ece8178d7665cad2fead951"
VARIANT = "checked-dispatch-completed-frozen-shared-v1"
SOURCE = {"src/decode/probe.rs", "src/decode/scratch.rs", "src/sketch/dispatch.rs"}
PROBE = "bulksketch::decode::probe::_::"
DISPATCH = "bulksketch::sketch::dispatch::"
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar", "-print-error-emitters",
         "-split-files", "-dest"]
SHARED = {f"bridge/Arithmetic/{name}.lean" for name in (
    "RowDispatchGenerated", "CompletedResultGenerated", "CanonicalizeGenerated", "ReconstructionRuntime",
    "DegreeProbeGenerated", "DirectTwoGenerated", "ReconstructionTypes")}
CAPTURES = {
    "probe": ("4d1373c954d72d070401dc406922afb095af4947d3081dc194f0793ba2855ae6",
              [PROBE + "run_next"], [PROBE + method for method in ("run_next", "charge", "run_charged")],
              [("src/decode/probe.rs", "run_next", 69, 4, 78, 5), ("src/decode/probe.rs", "charge", 83, 4, 103, 5),
               ("src/decode/probe.rs", "run_charged", 106, 4, 164, 5)]),
    "wrapper": ("65768d7b30b23e196f39fb69d113ee6035a828b120db77fdf353854c2fb1e158",
                [DISPATCH + "run_probe"], [DISPATCH + "run_probe"],
                [("src/sketch/dispatch.rs", "run_probe", 224, 0, 244, 1)]),
    "completed": ("967f971106c8c1e83170ff6d4179a4901986b2db72f110cd35d193dffed5edbe",
                  [DISPATCH + "_::completed_result"], [DISPATCH + "_::completed_result"],
                  [("src/sketch/dispatch.rs", "completed_result", 171, 4, 186, 5)]),
}
REJECT = {
    "stock": ("175:8-186:5", "interp/Invariants.ml, line 212"),
    "flag-off": ("175:8-186:5", "interp/Invariants.ml, line 212"),
    "unchecked": ("171:4-186:5", "interp/InterpBorrows.ml, line 1542"),
    "wrong-site": ("175:9-186:5", "interp/Invariants.ml, line 212"),
    "wrong-assert": ("177:17-177:70", "interp/Invariants.ml, line 212"),
    "wrong-workspace": ("175:8-186:5", "interp/Invariants.ml, line 212"),
}
ACCEPT = {"checked", "replay", "strict", "compatibility"}
OUTPUTS = {"Types.lean", "Funs.lean", "FunsExternal_Template.lean"}
COMPATIBILITY = Path("extraction/row-dispatch/Arithmetic")
PROBE_DOC = "[bulksketch::decode::probe::{bulksketch::decode::probe::Probe}::"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def blocks(path):
    return re.findall(r"^/-- .*?(?=^/-- |^end bulksketch)", path.read_text(), re.M | re.S)


def generated(root, lane, names):
    return {name: sha(root / DIRECTORY / lane / "Arithmetic" / name) for name in names}


def check(root=ROOT, entry="probe"):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    require(receipt["artifacts"] == ARTIFACTS, "public lifecycle artifact receipt differs")
    for item, digest in ARTIFACTS.items():
        require(sha(root / DIRECTORY / item) == digest, "public lifecycle artifact differs: " + str(DIRECTORY / item))
    require(set(receipt["source_sha256"]) == SOURCE and set(receipt["shared_sha256"]) == SHARED,
            "public lifecycle source bindings incomplete")
    seen_sources = set()
    for lane, (capture_hash, roots, includes, spans) in CAPTURES.items():
        path = root / DIRECTORY / lane / "arithmetic.llbc"
        require(sha(path) == capture_hash, "public lifecycle original capture differs: " + lane)
        data = json.loads(path.read_text())
        crate = data["translated"]
        opts = crate["options"]
        require(data["has_errors"] is False and opts["skip_borrowck"] is False
                and opts["start_from"] == roots and opts["include"] == includes,
                "public lifecycle capture options differ: " + lane)
        for row in crate["files"]:
            if row and row["name"].get("Local") in SOURCE:
                name = row["name"]["Local"]
                expected = receipt["source_sha256"][name]
                require(sha256(row["contents"].encode()).hexdigest() == expected
                        and sha(root.parents[1] / name) == expected, "public lifecycle source differs: " + name)
                seen_sources.add(name)
        declared = {}
        for fn in crate["fun_decls"]:
            if not fn or not isinstance(fn["body"], dict) or "Structured" not in fn["body"]:
                continue
            where = fn["item_meta"]["span"]["Untagged"]
            position = where["data"]
            source = crate["files"][position["file_id"]]["name"].get("Local")
            method = fn["item_meta"]["name"][-1].get("Ident", [""])[0]
            if (source, method) not in {(span[0], span[1]) for span in spans}:
                continue
            declared[source, method] = (position["beg"]["line"], position["beg"]["col"],
                                         position["end"]["line"], position["end"]["col"])
        require(declared == {(src, method): tuple(loc) for src, method, *loc in spans},
                "public lifecycle original structured spans differ: " + lane)
        if lane != "completed":
            ch, original = receipt["stock"][lane]["capture"]
            replay = receipt["stock"][lane]["replay"]
            outputs = OUTPUTS | {"TypesExternal_Template.lean"}
            require(ch["exit_code"] == original["exit_code"] == replay["status"] == 0
                    and original["argv"][1:-2] == replay["command"][1:-2] == FLAGS
                    and original["argv"][-1] == replay["command"][-1]
                    and replay["outputs"] == generated(root, lane, outputs),
                    "public lifecycle stock checked replay differs: " + lane)
    require(seen_sources == SOURCE, "public lifecycle embedded sources incomplete")
    for item, digest in receipt["shared_sha256"].items():
        require(sha(root / item) == digest, "public lifecycle shared binding differs: " + item)
    completed = receipt["completed"]
    require(completed["variant_id"] == VARIANT and completed["native_source_edited"] is False
            and completed["aeneas_commit"] == "ab34bd28458a08c150b7cbf1873e59af74588138"
            and completed["charon_commit"] == "7b462d9159db2ed3015162352183906a30bfafc6"
            and completed["build_exit_code"] == 0 and completed["build_command"][-3:] == ["-j", "2", "./main.exe"]
            and completed["base_source_sha256"] == {"src/interp/InterpJoin.ml":
                "57c5478aae42f8a354755424b67f67f37dc8bd233d653c97de0dcbbea5dd6229"}
            and completed["modified_source_sha256"] == {"src/interp/InterpJoin.ml": PATCHED_SOURCE}
            and sha(root / DIRECTORY / PATCH) == PATCH_SHA, "public lifecycle checked variant differs")
    ch, original = completed["capture"]
    require(ch["exit_code"] == 0 and original["exit_code"] == 1 and original["argv"][1:-2] == FLAGS,
            "public lifecycle completed-result stock capture differs")
    controls = completed["controls"]
    require(set(controls) == set(REJECT) | ACCEPT, "public lifecycle completed-result matrix incomplete")
    for label, row in controls.items():
        log_path = root / DIRECTORY / "completed" / (label + ".log")
        flags = [item for item in FLAGS[:-1] if item != "-checks" or label != "unchecked"]
        if label == "strict":
            flags.append("-strict-joins")
        flags.append("-dest")
        require(row["command"][1:-2] == flags and row["status"] == (1 if label in REJECT else 0)
                and row["flag"] == (label not in {"stock", "flag-off"})
                and row["binary_sha256"] == (BASE_BINARY if label == "stock" else PATCHED_BINARY)
                and row["log_sha256"] == sha(log_path) and row["input_sha256"] == CONTROL_INPUTS[label],
                "public lifecycle completed-result guard matrix differs: " + label)
        if label in REJECT:
            span, compiler = REJECT[label]
            log = log_path.read_text()
            require(f"Source: 'src/sketch/dispatch.rs', lines {span}" in log and compiler in log
                    and "Could not translate the body" in log, "public lifecycle rejection differs: " + label)
        elif label == "compatibility":
            require(row["outputs"] == {file: sha(root / COMPATIBILITY / file) for file in OUTPUTS},
                    "public lifecycle unrelated output differs")
        else:
            require(row["outputs"] == generated(root, "completed", OUTPUTS),
                    "public lifecycle checked output differs: " + label)
    type_blocks = blocks(root / DIRECTORY / "probe/Arithmetic/Types.lean")
    fun_blocks = blocks(root / DIRECTORY / "probe/Arithmetic/Funs.lean")
    selected = [b for b in type_blocks if PROBE_DOC + "run_charged::" in b.splitlines()[0]]
    selected += [b for b in fun_blocks if any(PROBE_DOC + method in b.splitlines()[0]
                                               for method in ("run_charged", "charge]", "run_next]"))]
    wrapper = [b for b in blocks(root / DIRECTORY / "wrapper/Arithmetic/Funs.lean")
               if b.startswith("/-- [" + DISPATCH + "run_probe]")]
    dispatch = [b for b in blocks(root / DIRECTORY / "completed/Arithmetic/Funs.lean")
                if b.startswith("/-- [bulksketch::sketch::dispatch::{bulksketch::sketch::dispatch::DecodeExecution<F>}::completed_result]")]
    require(len(selected) == 13 and len(wrapper) == 1 and len(dispatch) == 1
            and (root / TINY).read_text() == TINY_HEADER + "".join(selected) + WRAPPER_HEADER + wrapper[0] + "end bulksketch\n"
            and (root / COMPLETED).read_text() == COMPLETED_HEADER + dispatch[0] + "end bulksketch\n",
            "public lifecycle compiled projection differs")
    require(entry in {"probe", "completed"}, "unknown public lifecycle entry")
    active = TINY if entry == "probe" else COMPLETED
    raw = DIRECTORY / ("probe" if entry == "probe" else "completed") / "Arithmetic/Funs.lean"
    return {"compiled_projection": str(active), "projection_file_sha256": sha(root / active),
            "raw_generated_file": str(raw), "raw_file_sha256": sha(root / raw),
            "source_declarations_retained_verbatim": len(selected) + len(wrapper) if entry == "probe" else len(dispatch),
            "native_source_edited": False, "shared_types_and_function_dictionary_declarations_checked": True,
            **({"translator_variant": VARIANT} if entry == "completed" else {}),
            "controls": {label: row["status"] for label, row in controls.items()}}

TINY_HEADER = '-- Original checked tiny probe and backend wrapper.\nimport Arithmetic.RowDispatchGenerated\nimport Arithmetic.CanonicalizeGenerated\nimport Arithmetic.ReconstructionRuntime\nimport Arithmetic.DegreeProbeGenerated\nimport Arithmetic.DirectTwoGenerated\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.dupNamespace false\nset_option linter.unusedVariables false\nset_option maxHeartbeats 1000000\nset_option maxRecDepth 2048\n\nnamespace bulksketch\n\nlocal notation "core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all" =>\n  ReconstructionRuntime.sliceAll\nlocal notation "core.slice.Slice.windows" => CanonicalizeRuntime.windows\nlocal notation "core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice" =>\n  (fun (_ : Type) => ())\nlocal notation "core.iter.traits.iterator.Iterator.any.default" => CanonicalizeRuntime.anyWindows\n\n'
WRAPPER_HEADER = 'variable (dictionaries : RowDispatchRuntime.Dictionaries)\nlocal notation "backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels" => dictionaries.portable\nlocal notation "backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels" => dictionaries.pclmul\nlocal notation "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels" => dictionaries.vpclmul512\n\n'
COMPLETED_HEADER = '-- Original checked public DecodeExecution result dispatch.\nimport Arithmetic.RowDispatchGenerated\nimport Arithmetic.CompletedResultGenerated\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.dupNamespace false\nset_option linter.unusedVariables false\n\nnamespace bulksketch\n\nvariable (dictionaries : RowDispatchRuntime.Dictionaries)\nlocal notation "backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels" => dictionaries.portable\nlocal notation "backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels" => dictionaries.pclmul\nlocal notation "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels" => dictionaries.vpclmul512\n\n'
CONTROL_INPUTS = {'wrong-site': '7c724bc9c30566f32e4536c4bb8f4fd6fba1c91198991e263ec4731913fbf797', 'wrong-assert': '6a2c0a476c316d32345a82efbb133e0e02b79f74ad6a4cd1d8f629007f2935fb', 'wrong-workspace': '7f3906f7d2d58343de1f762f29948ab1f7af628424919c587846e493d318bd6b', 'stock': '967f971106c8c1e83170ff6d4179a4901986b2db72f110cd35d193dffed5edbe', 'flag-off': '967f971106c8c1e83170ff6d4179a4901986b2db72f110cd35d193dffed5edbe', 'unchecked': '967f971106c8c1e83170ff6d4179a4901986b2db72f110cd35d193dffed5edbe', 'checked': '967f971106c8c1e83170ff6d4179a4901986b2db72f110cd35d193dffed5edbe', 'replay': '967f971106c8c1e83170ff6d4179a4901986b2db72f110cd35d193dffed5edbe', 'strict': '967f971106c8c1e83170ff6d4179a4901986b2db72f110cd35d193dffed5edbe', 'compatibility': '64f6c9091c3332293354e889b3ce4d932e82df63cc7ff79b04b26964fda174ca'}
ARTIFACTS = {'probe/arithmetic.llbc': '4d1373c954d72d070401dc406922afb095af4947d3081dc194f0793ba2855ae6',
 'probe/charon.log': 'd382aa19ff718c8afc51e415c225efeb5667a4e5d25e7f3388b896967889a28e',
 'probe/stock.log': 'd9bf1ab49eb49bc890371d13ade455279d5ac1e80f247c6570d05fb5847a6ffb',
 'probe/replay.log': 'f215f2adaded0f1f6d17117d7391bd2099ea2d7f2c87da6265b9bf02a4be28d7',
 'probe/Arithmetic/Funs.lean': 'dba7b0e8301534b34901515c5ec6f1d4c9c078debc65ee960196c81a8122417f',
 'probe/Arithmetic/FunsExternal_Template.lean': 'f9de5b08fa080c092f0d8babd8adad210878a3fb64438e8e220f4e4b784ed5ac',
 'probe/Arithmetic/Types.lean': '75d69ee2a4d7f6ab801709f0149e54c27f705484fccd62bf60ecf7ab42fafcfa',
 'probe/Arithmetic/TypesExternal_Template.lean': '12df4e969ad798941839c2fa7e775bbe89c0e2abe536e6ecf02af266dc758d3d',
 'wrapper/arithmetic.llbc': '65768d7b30b23e196f39fb69d113ee6035a828b120db77fdf353854c2fb1e158',
 'wrapper/charon.log': '4e787e26b02bff13d349c543dcbeada5cda87bcf6f4f18ea05a981e61e6aad3a',
 'wrapper/stock.log': 'd08c6dce74b2bff8455f48f97346596cb84b7e41c85df1e0d37658ad77de8e22',
 'wrapper/replay.log': 'a32eae3aa53a5aba9d781a50cd50b73f6989bece9af5d66644c99314ea727825',
 'wrapper/Arithmetic/Funs.lean': '93d67758b75f68bfa5db10b10609766d37dc3fedaa6d7a8045e7b5e1b310bd5a',
 'wrapper/Arithmetic/FunsExternal_Template.lean': '1c1195488e06b150156e1cb1b80f4b5e6108892622fb3d48a9461758cabaecbf',
 'wrapper/Arithmetic/Types.lean': '047b7cb54d29be7afc034b56f14f4c4e8eeb89b7ddd28c2fd4a67d7f0e195272',
 'wrapper/Arithmetic/TypesExternal_Template.lean': '7280e96675403cf7a53494524e419cad8b13a094a8fd95dadec4ff0dd5168b04',
 'completed/arithmetic.llbc': '967f971106c8c1e83170ff6d4179a4901986b2db72f110cd35d193dffed5edbe',
 'completed/charon.log': '413f9c24b36d25e7ca7cbfb28d5e334de1eb0223260f19d4f79e8d09d63bbbce',
 'completed/Arithmetic/Funs.lean': '096778048a93fc27fb1285a6f2e52957306543548e8c9ee679d752aab6244daf',
 'completed/Arithmetic/FunsExternal_Template.lean': '616558ca3b403eb2dcd8ba686a7196c655b4592c9453eb7344cd5d68830c3be6',
 'completed/Arithmetic/Types.lean': '499b80e6ac842c2a765aa121c1d3696bdf45ad4de2e242bcbbfc174d6ac306fe',
 'completed/checked-dispatch-result.patch': 'bb8a1b98d1f263072d61379f471bd94e8a774e78d359022aa0aa3a03bf95518c',
 'completed/build.log': 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
 'completed/wrong-site.log': '65a6aac35591fcdf6a4d9f0083a8489657c4b83ea0e20138072e9f4c04c5395d',
 'completed/wrong-assert.log': '96f25654cc0118d13202c19494a48095890d5986d6f851d2e71a6a9dc02b1275',
 'completed/wrong-workspace.log': '8f6b1c0e0392a019951e4b4e991fae39e18905abb6eda13e91686d49844343c7',
 'completed/stock.log': '80e9e2b73cb97def19f3436162f407e7602e3e331fd2f954a9831a7be5f065ed',
 'completed/flag-off.log': '8cbfa6cbdd0a21ae8fdd2a4e1c7d8412854d7dc0f5e14f6fa0eb4e79c5af5d55',
 'completed/unchecked.log': '1dcce8d2950658bfc957bfceb6a06c77d130afee88e8130824a1048fe38f6360',
 'completed/checked.log': '5e281c26400757bd66295f10ee94aa2351a413a4cb4d5a1686a5bce188a63b4b',
 'completed/replay.log': '44a7adb19a3a3d35848812faa4f79fcbc7d81850753e698b3ea43b683e45ac89',
 'completed/strict.log': '54aec1ed8c360b5a72cfb838ba75a1811414b47c06b73983d72d8278d442ab96',
 'completed/compatibility.log': 'ffd15144178d09ef53a694bb6c4b96206bf7a80e51783b40d36d37b0324ac97b',
 'completed/scope_controls.py': '0f025f3730adde80ac0d8f1496fd7867eb057858c187a905ffd08a2a1cc64cbe'}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--entry", choices=("probe", "completed"), default="probe")
    print(json.dumps(check(entry=parser.parse_args().entry), indent=2))
