-- Diagnostic projection of the exact pure extraction bodies.
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

/-- [bulksketch::backend::x86_vpclmul512::load]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 196:0-200:1 -/
def backend.x86_vpclmul512.load
  (words : Slice Std.U64) : Result core.core_arch.x86.__m512i := do
  let i := Slice.len words
  let i1 ← backend.x86_vpclmul512.mask i
  let p ← core.slice.Slice.as_ptr words
  let p1 ← core.ptr.const_ptr.RawPtrConstT.cast Std.I64 p
  core.core_arch.x86.avx512f._mm512_maskz_loadu_epi64 i1 p1

/-- [bulksketch::backend::x86_vpclmul512::store]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 203:0-206:1 -/
def backend.x86_vpclmul512.store
  (words : Slice Std.U64) (value : core.core_arch.x86.__m512i) :
  Result (Slice Std.U64)
  := do
  let (p, words1) ← core.slice.Slice.as_mut_ptr words
  let p1 ← core.ptr.mut_ptr.RawPtrMutT.cast Std.I64 p
  let i := Slice.len words1
  let i1 ← backend.x86_vpclmul512.mask i
  core.core_arch.x86.avx512f._mm512_mask_storeu_epi64 p1 i1 value
  ok words1

end

end BulksketchBridge.X86MaskedMemory.PureExtraction
