#!/usr/bin/env python3
"""Check exact scalar wire difference and inherited backend dictionaries."""
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("extraction/default-wire-difference")
PROJECTION = Path("bridge/Arithmetic/DefaultWireDifferenceGenerated.lean")
DICTIONARIES = Path("bridge/Arithmetic/DefaultWireDifferenceDictionariesGenerated.lean")
SOURCES = {"src/backend/contract.rs", "src/backend/portable.rs", "src/backend/x86_pclmul.rs"}
SHARED = {f"bridge/Arithmetic/{name}.lean" for name in
          ("AvxLinearEntryGenerated", "MutableZipRuntime", "RowDispatchGenerated")}
SELECTOR = "bulksketch::backend::contract::BulkKernels::difference"
BACKENDS = ["bulksketch::backend::portable::Portable", "bulksketch::backend::x86_pclmul::Pclmul"]
IMPLS = ["{impl bulksketch::backend::contract::BulkKernels for " + name + "}" for name in BACKENDS]
CLONES = ["{impl core::clone::Clone for " + name + "}::clone" for name in BACKENDS]
MARKER = "/-- [" + SELECTOR + "]"
FLAGS = ["-backend", "lean", "-checks", "-sequential", "-no-progress-bar",
         "-print-error-emitters", "-split-files", "-dest"]
PINNED = {
    "default": ("e373e0fe458117d42d261d5f273b2c69f75c4d783793bf022cf1e641b2722f24",
                "0fbabac7637b044f6b400eb8f5a9908024d3b2f38b683118abe6ecb0c073a739"),
    "dictionaries": ("82f1decba6321c24739626496ca61d06a6f20f1e18e143cc7d7ec154fb07e1b6",
                     "a7bf2e963f6a2103022ff05f7a3c54368df4d3d83749eb684e61253bcc0aa0fc"),
}
TEMPLATES = {"Funs.lean", "Types.lean", "FunsExternal_Template.lean"}
DICT_DECL = re.compile(
    r"^(?:impl_)?def (backend\.(?:portable\.Portable|x86_pclmul\.Pclmul)\.Insts\."
    r"(?:CoreCloneClone(?:\.clone)?|CoreMarkerCopy|BulksketchBackendContractArithmetic|"
    r"BulksketchBackendContractBulkKernels))\s*(?:\{|:|\n)", re.M,
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def blocks(text):
    return re.findall(r"^/-- .*?(?=^/-- |^end bulksketch)", text, re.M | re.S)


def check(root=ROOT):
    receipt = json.loads((root / DIRECTORY / "receipt.json").read_text())
    parent = json.loads((root / "extraction/avx-recurrence/receipt.json").read_text())
    require(receipt["native_source_edited"] is False and
            all(receipt[key] == parent[key] for key in ("source_commit", "rust_toolchain", "target",
                "aeneas_commit", "charon_commit", "tool_binary_sha256")),
            "default wire difference tool receipt differs")
    require(set(receipt["captures"]) == set(PINNED) and set(receipt["source_sha256"]) == SOURCES,
            "default wire difference incomplete capture")
    files = set()
    emitted = {}
    for label, (capture_sha, funs_sha) in PINNED.items():
        directory = DIRECTORY / label
        outputs = TEMPLATES | ({"TypesExternal_Template.lean"} if label == "dictionaries" else set())
        files.update(str(directory / name) for name in
                     {"arithmetic.llbc", "aeneas.log", "charon.log", "replay.log"} |
                     {"Arithmetic/" + name for name in outputs})
        capture_path, funs_path = root / directory / "arithmetic.llbc", root / directory / "Arithmetic/Funs.lean"
        require(sha(capture_path) == capture_sha,
                "default wire difference original capture differs: " + str(directory / "arithmetic.llbc"))
        require(sha(funs_path) == funs_sha,
                "default wire difference original capture differs: " + str(directory / "Arithmetic/Funs.lean"))
        capture = json.loads(capture_path.read_text())
        crate = capture["translated"]
        options = crate["options"]
        expected_roots = [SELECTOR] if label == "default" else [SELECTOR, *IMPLS, *CLONES]
        expected_includes = [SELECTOR] if label == "default" else [SELECTOR, *IMPLS, *BACKENDS, *CLONES]
        require(capture["has_errors"] is False and options["skip_borrowck"] is False
                and options["start_from"] == expected_roots and options["include"] == expected_includes,
                "default wire difference extraction options differ: " + label)
        selected = receipt["captures"][label]
        charon, aeneas = (selected["commands"][name] for name in ("charon", "aeneas"))
        replay = selected["replay"]
        require(charon["exit_code"] == aeneas["exit_code"] == replay["exit_code"] == 0
                and charon["command"][4].removeprefix("--dest-file=") == aeneas["command"][-1] == replay["command"][-1]
                and charon["command"][-2:] == ["--target", receipt["target"]]
                and [v.removeprefix("--start-from=") for v in charon["command"] if v.startswith("--start-from=")] == expected_roots
                and [v.removeprefix("--include=") for v in charon["command"] if v.startswith("--include=")] == expected_includes
                and aeneas["command"][1:-2] == replay["command"][1:-2] == FLAGS
                and replay["identical_outputs"] is True
                and replay["outputs_sha256"] == {name: sha(root / directory / "Arithmetic" / name) for name in outputs},
                "default wire difference checked replay differs: " + label)
        expected_sources = {"src/backend/contract.rs"} if label == "default" else SOURCES
        for source in expected_sources:
            originals = [file["contents"] for file in crate["files"] if file and file["name"] == {"Local": source}]
            expected = receipt["source_sha256"][source]
            require(len(originals) == 1 and sha256(originals[0].encode()).hexdigest() == expected
                    and sha(root.parents[1] / source) == expected, "default wire difference source differs: " + source)
        found = []
        for fun in crate["fun_decls"]:
            if not fun or fun["item_meta"]["name"][-1].get("Ident", [""])[0] != "difference":
                continue
            span = fun["item_meta"]["span"]["Untagged"]["data"]
            if crate["files"][span["file_id"]]["name"] == {"Local": "src/backend/contract.rs"}:
                found.append((fun, span))
        require(len(found) == 1 and found[0][1]["beg"] == {"line": 103, "col": 4}
                and found[0][1]["end"] == {"line": 118, "col": 5}
                and "Structured" in found[0][0]["body"], "default wire difference source span differs")
        if label == "dictionaries":
            matches = {}
            for instance in crate["trait_impls"]:
                if instance is None:
                    continue
                span = instance["item_meta"]["span"]["Untagged"]["data"]
                source = crate["files"][span["file_id"]]["name"].get("Local", "")
                if (source, span["beg"]["line"]) in {("src/backend/portable.rs", 84), ("src/backend/x86_pclmul.rs", 97)}:
                    matches[source] = [m["skip_binder"]["id"] for m in instance["methods"]
                                       if m["kind"] == {"TraitMethod": [0, 6]}]
            require(matches == {source: [found[0][0]["def_id"]] for source in SOURCES - {"src/backend/contract.rs"}},
                    "default wire difference inheritance differs")
        emitted[label] = funs_path.read_text()
    require(set(receipt["artifacts"]) == files, "default wire difference receipt artifact set differs")
    for file, digest in receipt["artifacts"].items():
        require(sha(root / file) == digest, "default wire difference artifact differs: " + file)
    require(set(receipt["shared_sha256"]) == SHARED, "default wire difference shared bindings incomplete")
    for file, digest in receipt["shared_sha256"].items():
        require(sha(root / file) == digest, "default wire difference shared binding differs: " + file)
    default = ["".join(block for block in blocks(text) if block.startswith(MARKER))
               for text in emitted.values()]
    require(len(default) == 2 and default[0] == default[1] and default[0].count(MARKER) == 3
            and (root / PROJECTION).read_text() == DEFAULT_HEADER + default[0] + "end bulksketch\n",
            "default wire difference projected body differs")
    retained = [(DICT_DECL.search(block).group(1), block) for block in blocks(emitted["dictionaries"])
                if DICT_DECL.search(block)]
    require(len(retained) == 10 and (root / DICTIONARIES).read_text() ==
            DICTIONARY_HEADER + "".join(block for _, block in retained) + "end bulksketch\n",
            "default wire difference dictionary projection differs")
    types = (root / DIRECTORY / "dictionaries/Arithmetic/Types.lean").read_text()
    for filename, name in (("AvxLinearEntryGenerated", "portable.Portable"),
                           ("RowDispatchGenerated", "x86_pclmul.Pclmul")):
        exact_type = [block.rstrip() for block in blocks(types) if f"def backend.{name} := Unit" in block]
        require(len(exact_type) == 1 and exact_type[0] in
                (root / f"bridge/Arithmetic/{filename}.lean").read_text(),
                "default wire difference dictionary backend type differs: " + name)
    return {"raw_generated_file": str(DIRECTORY / "default/Arithmetic/Funs.lean"),
            "raw_file_sha256": PINNED["default"][1], "compiled_projection": str(PROJECTION),
            "projection_file_sha256": sha(root / PROJECTION), "dictionary_projection": str(DICTIONARIES),
            "dictionary_projection_sha256": sha(root / DICTIONARIES),
            "source_declarations_retained_verbatim": 13, "native_source_edited": False,
            "generated_declarations": ["bulksketch.backend.contract.BulkKernels.difference." + name
                for name in ("default_loop.body", "default_loop", "default")] +
                ["bulksketch." + name for name, _ in retained],
            "shared_types_and_function_dictionary_declarations_checked": True}

DEFAULT_HEADER = '-- Exact original BulkKernels difference with scoped nested Zip bindings.\nimport Arithmetic.DefaultWireDifferenceRuntime\n\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.dupNamespace false\nset_option linter.unusedVariables false\n\nnamespace bulksketch\n\nlocal notation "core.iter.traits.iterator.Iterator.zip.trait_default" =>\n  BulksketchBridge.DefaultWireDifferenceRuntime.zip\nlocal notation "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair" =>\n  BulksketchBridge.DefaultWireDifferenceRuntime.innerDictionary\nlocal notation "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next" =>\n  BulksketchBridge.DefaultWireDifferenceRuntime.next\n\n'
DICTIONARY_HEADER = '-- Exact original Portable and PCLMUL trait dictionaries.\nimport Arithmetic.DefaultWireDifferenceGenerated\nimport Arithmetic.AvxLinearEntryGenerated\nimport Arithmetic.AvxScalarDelegatesGenerated\nimport Arithmetic.OddRecurrenceGenerated\nimport Arithmetic.PortableEncodingGenerated\nimport Arithmetic.PortableHornerGenerated\nimport Arithmetic.PortableInverseGenerated\nimport Arithmetic.PortableSliceGenerated\nimport Arithmetic.PortableXorGenerated\nimport Arithmetic.RowDispatchGenerated\nimport Arithmetic.X86PclmulHornerGenerated\nimport Arithmetic.X86PclmulInsertGenerated\nimport Arithmetic.X86PclmulNextGenerated\nimport Arithmetic.X86PclmulSliceGenerated\n\nopen Aeneas Aeneas.Std Result\nset_option linter.dupNamespace false\nset_option linter.unusedVariables false\nset_option maxRecDepth 2048\nset_option maxHeartbeats 2000000\n\nnamespace bulksketch\n\n'

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
