#!/usr/bin/env python3
"""Check the original degree certificate extraction and scoped Lean bindings."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = Path("extraction/degree-certificate")
RAW = EXTRACTION / "Arithmetic"
ACTIVE = Path("bridge/Arithmetic/CertificateGenerated.lean")
RUNTIME = Path("bridge/Arithmetic/CertificateRuntime.lean")
PATCH = Path("tooling/aeneas-ended-projector/ended-projector-leaf.patch")
SOURCE = Path("src/decode/deg34.rs")
SOURCE_SHA = "50e92cc158d33b58361cf95719d4f13e01295802a15e1dab7622fab5ce050015"
SELECTOR = "bulksketch::decode::deg34::certificate"
VARIANT = "checked-ended-projector-leaf-v1"
CLOSURE = "decode.deg34.certificate.closure"
FN_MUT = CLOSURE + ".Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0U64Bool"
FN_ONCE = CLOSURE + ".Insts.CoreOpsFunctionFnOnceTuplePairUsizeShared0U64Bool"
FUNCTIONS = [
    "core.ops.range.RangeInclusive.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator",
    FN_MUT + ".call_mut", FN_ONCE + ".call_once", FN_ONCE, FN_MUT,
    "decode.deg34.certificate_loop0_loop0.body", "decode.deg34.certificate_loop0_loop0",
    "decode.deg34.certificate_loop0.body", "decode.deg34.certificate_loop0",
    "decode.deg34.certificate",
]
SHARED_TYPES = ["types.RawProduct", "types.FieldId", "field.sealed.Sealed", "field.BinaryField",
                "backend.contract.Arithmetic", "backend.contract.BulkKernels"]
SHARED_TYPE_PATHS = [Path("bridge/Arithmetic/Types.lean"), Path("bridge/Arithmetic/SliceKernelTypes.lean")]
SLICE_EQ = "Slice.Insts.CoreCmpPartialEqSlice"
EXTERNALS = ["Mut1A.Insts.CoreCmpPartialEqShared0B.eq", "core.iter.traits.iterator.Iterator.any.default",
             "core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any",
             "core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.any", "core.slice.raw.from_ref"]
ARTIFACTS = {str(EXTRACTION / name) for name in ("arithmetic.llbc", "charon.log", "aeneas.log",
    "aeneas-pinned-rejection.log", "Arithmetic/Types.lean", "Arithmetic/Funs.lean",
    "Arithmetic/FunsExternal_Template.lean")}
HEADER = """-- Exact original-source declaration projection. Imports and scoped external bindings are adapted only.
module
public import Arithmetic.RebuiltLfsrGenerated
public import Arithmetic.CertificateRuntime
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

local notation "core.iter.traits.iterator.Iterator.any.default" => Aeneas.Std.CertificateRuntime.any
local notation "Mut1A.Insts.CoreCmpPartialEqShared0B.eq" => Aeneas.Std.CertificateRuntime.mutableSharedEq

"""


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(path):
    body = path.read_text().split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    declarations = {}
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        names = re.findall(r"(?m)^(?:def|impl_def|structure|inductive|abbrev)\s+(\S+)", block)
        require(len(names) == 1 and names[0] not in declarations, "unexpected generated declaration in " + str(path))
        declarations[names[0]] = block.strip()
    return declarations


def check(root=ROOT):
    receipt = json.loads((root / EXTRACTION / "receipt.json").read_text())
    require(receipt["status"] == "generated" and receipt["selected_roots"] == [SELECTOR]
            and receipt["llbc_has_errors"] is False and receipt["translator_variant"] == VARIANT,
            "invalid certificate extraction receipt")
    artifacts = receipt["artifacts"]
    require(len(artifacts) == len(ARTIFACTS) and {entry["path"] for entry in artifacts} == ARTIFACTS,
            "incomplete certificate extraction artifacts")
    for entry in artifacts:
        require(sha(root / entry["path"]) == entry["sha256"], "raw certificate artifact differs: " + entry["path"])
    require(sha(root / RUNTIME) == receipt["runtime_sha256"], "scoped certificate runtime differs")
    require(sha(root / PATCH) == receipt["patch_sha256"], "certificate translator patch differs")
    require(sha(root.parents[1] / SOURCE) == SOURCE_SHA, "frozen certificate Rust source differs")
    llbc = json.loads((root / EXTRACTION / "arithmetic.llbc").read_text())
    translated = llbc["translated"]
    require(llbc["has_errors"] is False and translated["options"]["start_from"] == [SELECTOR]
            and translated["options"]["opaque"] == [], "incomplete or altered certificate LLBC")
    targets = translated["target_information"]
    require(len(targets) == 1 and targets[0]["key"] == "x86_64-apple-darwin"
            and targets[0]["value"]["target_pointer_size"] == 8, "unexpected certificate target")
    path = [{"Ident": [part, 0]} for part in SELECTOR.split("::")]
    matching = [fn for fn in translated["fun_decls"] if fn and fn["item_meta"]["name"] == path]
    require(len(matching) == 1 and "Structured" in matching[0]["body"], "certificate body missing from LLBC")
    span = matching[0]["item_meta"]["span"]["Untagged"]["data"]
    source = translated["files"][span["file_id"]]
    require(span["beg"] == {"line": 112, "col": 0} and span["end"] == {"line": 136, "col": 1}
            and source["name"] == {"Local": str(SOURCE)}
            and hashlib.sha256(source["contents"].encode()).hexdigest() == SOURCE_SHA,
            "certificate LLBC source span or contents differ")
    types = blocks(root / RAW / "Types.lean")
    require(list(types) == [*SHARED_TYPES, CLOSURE], "certificate type closure changed")
    shared = {}
    for source_path in SHARED_TYPE_PATHS:
        shared.update(blocks(root / source_path))
    require(all(types[name] == shared[name] for name in SHARED_TYPES), "certificate shared type differs")
    functions = blocks(root / RAW / "Funs.lean")
    retained = [name for name in functions if name in FUNCTIONS]
    require(retained == FUNCTIONS, "certificate declarations changed")
    require(re.findall(r"(?m)^axiom\s+(\S+)", (root / RAW / "FunsExternal_Template.lean").read_text())
            == EXTERNALS, "certificate external declaration set changed")
    original_eq = functions[SLICE_EQ]
    reused_eq = blocks(root / "bridge/Arithmetic/RebuiltLfsrGenerated.lean")[SLICE_EQ]
    # The prior declaration adds the unused ne method. The retained eq field is identical.
    require(reused_eq.split("\n  ne :=", 1)[0].replace("\nimpl_def ", "\ndef ") + "\n}" == original_eq,
            "certificate slice equality dictionary differs")
    projected = HEADER + "".join(block + "\n\n" for block in [types[CLOSURE], *(functions[n] for n in FUNCTIONS)])
    require((root / ACTIVE).read_text() == projected + "end bulksketch\n", "compiled certificate projection differs")
    return {
        "raw_generated_file": str(RAW / "Funs.lean"), "raw_file_sha256": sha(root / RAW / "Funs.lean"),
        "compiled_projection": str(ACTIVE), "projection_file_sha256": sha(root / ACTIVE),
        "source_declarations_retained_verbatim": len(FUNCTIONS),
        "source_type_declarations_retained_verbatim": 1,
        "shared_types_and_function_dictionary_declarations_checked": True,
        "generated_declarations": ["bulksketch." + name for name in FUNCTIONS],
        "translator_variant": VARIANT, "native_source_edited": False,
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
