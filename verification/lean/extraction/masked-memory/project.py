#!/usr/bin/env python3
"""Check exact pure extraction bodies used only for memory obstruction proofs."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
EXTRACTION = "extraction/masked-memory/"
GENERATED = "bridge/Arithmetic/X86MaskedMemoryPureGenerated.lean"
FILES = {EXTRACTION + path for path in ("arithmetic.llbc", "charon.log", "aeneas.log",
    "Arithmetic/Funs.lean", "Arithmetic/Types.lean", "Arithmetic/FunsExternal_Template.lean",
    "Arithmetic/TypesExternal_Template.lean")}
PREFIX = "backend.x86_vpclmul512."
HEADER = """-- Diagnostic projection of the exact pure extraction bodies.
module
public import Arithmetic.X86LaneMaskGenerated
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace BulksketchBridge.X86MaskedMemory.PureExtraction

/-- The pure extracted external signatures, supplied as parameters. -/
structure Bindings (V : Type) where
  asPtr : {T : Type} → Slice T → Result (ConstRawPtr T)
  asMutPtr : {T : Type} → Slice T → Result (MutRawPtr T × Slice T)
  castConst : {T : Type} → (U : Type) → ConstRawPtr T → Result (ConstRawPtr U)
  castMut : {T : Type} → (U : Type) → MutRawPtr T → Result (MutRawPtr U)
  load : U8 → ConstRawPtr I64 → Result V
  store : MutRawPtr I64 → U8 → V → Result Unit

section

variable {V : Type} (bindings : Bindings V)

local notation "core.core_arch.x86.__m512i" => V
local notation "backend.x86_vpclmul512.mask" => bulksketch.backend.x86_vpclmul512.mask
local notation "core.slice.Slice.as_ptr" => bindings.asPtr
local notation "core.slice.Slice.as_mut_ptr" => bindings.asMutPtr
local notation "core.ptr.const_ptr.RawPtrConstT.cast" => bindings.castConst
local notation "core.ptr.mut_ptr.RawPtrMutT.cast" => bindings.castMut
local notation "core.core_arch.x86.avx512f._mm512_maskz_loadu_epi64" => bindings.load
local notation "core.core_arch.x86.avx512f._mm512_mask_storeu_epi64" => bindings.store

"""
FOOTER = "end\n\nend BulksketchBridge.X86MaskedMemory.PureExtraction\n"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def projection(root):
    raw = (root / (EXTRACTION + "Arithmetic/Funs.lean")).read_text()
    body = raw.split("namespace bulksketch\n", 1)[1].rsplit("end bulksketch", 1)[0]
    names = []
    retained = []
    mask = (root / "bridge/Arithmetic/X86LaneMaskGenerated.lean").read_text()
    for block in re.findall(r"(?ms)^/--.*?(?=^/--|\Z)", body):
        found = re.search(r"^def\s+(\S+)", block, re.MULTILINE)
        if not found:
            raise ValueError("unrecognized masked memory declaration")
        names.append(found.group(1))
        if found.group(1) == PREFIX + "mask":
            if block.strip() not in mask:
                raise ValueError("shared source mask differs")
        else:
            retained.append(block)
    if names != [PREFIX + suffix for suffix in ("mask", "load", "store")]:
        raise ValueError("masked memory declaration set changed")
    return HEADER + "".join(retained) + FOOTER


def check(root=ROOT):
    receipt = json.loads((root / (EXTRACTION + "receipt.json")).read_text())
    if receipt["status"] != "diagnostic-generated" or receipt["native_body_proof_credit"] != 0 or \
            len(receipt["artifacts"]) != len(FILES) or \
            {item["path"] for item in receipt["artifacts"]} != FILES:
        raise ValueError("masked memory diagnostic receipt changed")
    for item in receipt["artifacts"]:
        if sha(root / item["path"]) != item["sha256"]:
            raise ValueError("raw masked memory extraction mismatch: " + item["path"])
    if json.loads((root / (EXTRACTION + "arithmetic.llbc")).read_text())["has_errors"] is not False:
        raise ValueError("incomplete masked memory LLBC")
    external = (root / (EXTRACTION + "Arithmetic/FunsExternal_Template.lean")).read_text()
    declarations = {
        name: " ".join(signature.split())
        for name, signature in re.findall(r"(?ms)^axiom\s+(\S+)\s+(.*?)(?=^/--|\Z)", external)
    }
    required = {
        "core.core_arch.x86.avx512f._mm512_maskz_loadu_epi64":
            ": Std.U8 → ConstRawPtr Std.I64 → Result core.core_arch.x86.__m512i",
        "core.core_arch.x86.avx512f._mm512_mask_storeu_epi64":
            ": MutRawPtr Std.I64 → Std.U8 → core.core_arch.x86.__m512i → Result Unit",
        "core.ptr.const_ptr.RawPtrConstT.cast":
            "{T : Type _} (U : Type _) : ConstRawPtr T → Result (ConstRawPtr U)",
        "core.ptr.mut_ptr.RawPtrMutT.cast":
            "{T : Type _} (U : Type _) : MutRawPtr T → Result (MutRawPtr U)",
        "core.slice.Slice.as_ptr": "{T : Type _} : Slice T → Result (ConstRawPtr T)",
        "core.slice.Slice.as_mut_ptr": "{T : Type _} : Slice T → Result ((MutRawPtr T) × (Slice T))",
    }
    if declarations != required:
        raise ValueError("pure masked memory effect signatures changed")
    if (root / GENERATED).read_text() != projection(root):
        raise ValueError("compiled masked memory obstruction projection differs")
    return {"compiled_projection": GENERATED, "projection_file_sha256": sha(root / GENERATED),
            "source_declarations_retained_verbatim": 2, "native_body_proof_credit": 0}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
