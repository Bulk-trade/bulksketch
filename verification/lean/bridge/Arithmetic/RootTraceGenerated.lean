-- Exact checked source projection. See extraction/root-trace for provenance.
import Arithmetic.RootSetupGenerated
import Arithmetic.DenseCoefficientGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace Aeneas.Std.RootTraceRuntime

/-- An external application slot for the still-unbound original Dense
modular-square method. The argument is explicit and introduces no axiom. -/
abbrev ModularSquare :=
  {F K : Type} → bulksketch.field.BinaryField F → bulksketch.backend.contract.BulkKernels K F →
    Slice U64 → Slice U64 → Slice U64 → Slice U64 → Slice bulksketch.types.RawProduct →
    Result (Usize × Slice U64 × Slice bulksketch.types.RawProduct)

/-- Rust Option insertion calls the closure only when absent. The closure's
captured mutable length and the writeback of the returned borrow are
both preserved in the extracted call shape. -/
structure FnOnceWithState (F Input Output : Type) where
  call_once : F → Input → Result (Output × F)

def getOrInsertWith {T F : Type}
    (once : FnOnceWithState F Unit T) (input : Option T) (closure : F) :
    Result (T × (T → Option T) × F) := do
  match input with
  | some value => .ok (value, some, closure)
  | none =>
    let (value, next) ← once.call_once closure ()
    .ok (value, some, next)

end Aeneas.Std.RootTraceRuntime

namespace bulksketch

set_option linter.dupNamespace false
set_option linter.unusedVariables false

variable (squareModel : Aeneas.Std.RootTraceRuntime.ModularSquare)

local notation "core.ops.function.FnOnce" => Aeneas.Std.RootTraceRuntime.FnOnceWithState
local notation "core.option.Option.get_or_insert_with" => Aeneas.Std.RootTraceRuntime.getOrInsertWith
local notation "poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into" => squareModel

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::trace::{closure}]
    Source: 'src/decode/roots.rs', lines 394:64-399:9 -/
def decode.roots.Roots.trace.closure (F : Type _) (K : Type _) :=
  Std.U64 × Std.U32

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::trace::{impl core::ops::function::FnOnce<(), [u64; 64usize]> for bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::trace::{closure}<'_0, '_1, F, K>}::call_once]:
    Source: 'src/decode/roots.rs', lines 394:64-399:9 -/
def
  decode.roots.Roots.trace.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU6464.call_once
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.roots.Roots.trace.closure F K) (_ : Unit) :
  Result ((Array Std.U64 64#usize) × (decode.roots.Roots.trace.closure F K))
  := do
  let (i, _) := c
  let basis := Array.repeat 64#usize 0#u64
  let i1 ← fieldBinaryFieldInst.MASK
  let i2 ← lift (i &&& i1)
  let i3 ← lift (core.cmp.impls.OrdU64.max i2 1#u64)
  let basis1 ← Array.update basis 0#usize i3
  ok (basis1, (i, 1#u32))

/-- Trait implementation: [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::trace::{impl core::ops::function::FnOnce<(), [u64; 64usize]> for bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::trace::{closure}<'_0, '_1, F, K>}]
    Source: 'src/decode/roots.rs', lines 394:64-399:9 -/
@[reducible]
def decode.roots.Roots.trace.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU6464
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnOnce (decode.roots.Roots.trace.closure F K) Unit (Array
  Std.U64 64#usize) := {
  call_once :=
    decode.roots.Roots.trace.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU6464.call_once
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::trace]: loop body 0:
    Source: 'src/decode/roots.rs', lines 402:8-408:9 -/
@[rust_loop_body]
def decode.roots.Roots.trace_loop0.body
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (i : Std.U32)
  (basis_len : Std.U32) (basis : Array Std.U64 64#usize) :
  Result (ControlFlow (Std.U32 × (Array Std.U64 64#usize)) (Std.U32 × (Array
    Std.U64 64#usize)))
  := do
  if basis_len <= i
  then
    let i1 ← lift (UScalar.cast .Usize basis_len)
    let i2 ← i1 - 1#usize
    let splitter ← Array.index_usize basis i2
    let i3 ← fieldBinaryFieldInst.BITS
    let i4 ← i3 - 1#u32
    let carry ← splitter >>> i4
    let i5 ← splitter <<< 1#i32
    let i6 ← fieldBinaryFieldInst.MASK
    let i7 ← lift (i5 &&& i6)
    let i8 ← lift (core.num.U64.wrapping_sub 0#u64 carry)
    let i9 ← fieldBinaryFieldInst.MODULUS_LOW
    let i10 ← lift (i9 &&& i8)
    let i11 ← lift (UScalar.cast .Usize basis_len)
    let i12 ← lift (i7 ^^^ i10)
    let a ← Array.update basis i11 i12
    let basis_len1 ← basis_len + 1#u32
    ok (cont (basis_len1, a))
  else ok (done (basis_len, basis))

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::trace]: loop 0:
    Source: 'src/decode/roots.rs', lines 402:8-408:9 -/
@[rust_loop]
def decode.roots.Roots.trace_loop0
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (i : Std.U32)
  (basis_len : Std.U32) (basis : Array Std.U64 64#usize) :
  Result (Std.U32 × (Array Std.U64 64#usize))
  := do
  loop
    (fun (basis_len1, basis1) => decode.roots.Roots.trace_loop0.body
      fieldBinaryFieldInst i basis_len1 basis1)
    (basis_len, basis)

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::trace]: loop body 1:
    Source: 'src/decode/roots.rs', lines 413:8-424:9 -/
@[rust_loop_body]
def decode.roots.Roots.trace_loop1.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (s : Slice Std.U64) (s1 : Slice Std.U64) (splitter : Std.U64)
  (iter : core.ops.range.Range Std.U32) (i : Std.Usize) (s2 : Slice Std.U64)
  (s3 : Slice Std.U64) (s4 : Slice types.RawProduct) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × Std.Usize × (Slice
    Std.U64) × (Slice Std.U64) × (Slice types.RawProduct)) (Std.Usize ×
    (Slice Std.U64) × (Slice Std.U64) × (Slice types.RawProduct)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done (i, s2, s3, s4))
  | some _ =>
    let s5 ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) s2
        { «end» := i }
    let (len, s6, s7) ←
      poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into
        fieldBinaryFieldInst backendcontractBulkKernelsInst s5 s s1 s3 s4
    let (s8, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) s2
        { «end» := len }
    let s9 ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) s6
        { «end» := len }
    let s10 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s8 s9
    let s11 := index_mut_back s10
    let (i1, s12) ←
      poly.Dense.Insts.BulksketchPolyPolynomial.xor_coefficient
        fieldBinaryFieldInst backendcontractBulkKernelsInst s11 len 1#usize
        splitter
    ok (cont (iter1, i1, s12, s6, s7))

local notation "decode.roots.Roots.trace_loop1.body" => (decode.roots.Roots.trace_loop1.body squareModel)

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::trace]: loop 1:
    Source: 'src/decode/roots.rs', lines 413:8-424:9 -/
@[rust_loop]
def decode.roots.Roots.trace_loop1
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.Range Std.U32) (i : Std.Usize) (s : Slice Std.U64)
  (s1 : Slice Std.U64) (s2 : Slice Std.U64) (s3 : Slice Std.U64)
  (s4 : Slice types.RawProduct) (splitter : Std.U64) :
  Result (Std.Usize × (Slice Std.U64) × (Slice Std.U64) × (Slice
    types.RawProduct))
  := do
  loop
    (fun (iter1, i1, s5, s6, s7) => decode.roots.Roots.trace_loop1.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst s s3 splitter iter1
      i1 s5 s6 s7)
    (iter, i, s1, s2, s4)

local notation "decode.roots.Roots.trace_loop1" => (decode.roots.Roots.trace_loop1 squareModel)

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::trace]:
    Source: 'src/decode/roots.rs', lines 384:4-443:5 -/
def decode.roots.Roots.trace
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.roots.Roots) (buffers : decode.roots.FactorWork)
  (meter : types.WorkMeter) :
  Result ((core.result.Result (core.result.Result types.Stage
    types.DecodeFailure) types.DecodeError) × decode.roots.Roots ×
    decode.roots.FactorWork × (decode.roots.FactorWork →
    decode.roots.FactorWork) × types.WorkMeter)
  := do
  let (r, meter1) ←
    decode.roots.charge meter (decode.work.Charge.Trace self.degree)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let i ← self.attempts + 1#usize
    let (basis, get_or_insert_with_back, c) ←
      core.option.Option.get_or_insert_with
        (decode.roots.Roots.trace.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU6464
        fieldBinaryFieldInst backendcontractBulkKernelsInst)
        buffers.basis.directions (self.splitter_seed, buffers.basis.len)
    let (_, basis_len) := c
    let (basis_len1, basis1) ←
      decode.roots.Roots.trace_loop0 fieldBinaryFieldInst self.direction
        basis_len basis
    let i1 ← lift (UScalar.cast .Usize self.direction)
    let splitter ← Array.index_usize basis1 i1
    let s ← core.slice.Slice.fill core.clone.CloneU64 buffers.trace 0#u64
    let s1 ← Slice.update s 1#usize splitter
    let i2 ← fieldBinaryFieldInst.BITS
    let (i3, s2, s3, s4) ←
      decode.roots.Roots.trace_loop1 fieldBinaryFieldInst
        backendcontractBulkKernelsInst { start := 1#u32, «end» := i2 }
        2#usize buffers.modulus s1 buffers.gcd buffers.table buffers.raw
        splitter
    if self.checked
    then
      let o := get_or_insert_with_back basis1
      ok (core.result.Result.Ok (core.result.Result.Ok types.Stage.Gcd),
        { self with trace_len := i3, attempts := i },
        {
          buffers
            with
            trace := s2,
            gcd := s3,
            raw := s4,
            basis := { directions := o, len := basis_len1 }
        }, fun buffers1 => buffers1, meter1)
    else
      let (r1, meter2) ←
        decode.roots.charge meter1 (decode.work.Charge.SplitCheck self.degree)
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let s5 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) s2
            { «end» := i3 }
        let (_, s6, s7) ←
          poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into
            fieldBinaryFieldInst backendcontractBulkKernelsInst s5
            buffers.modulus buffers.table s3 s4
        let (s8, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U64) s2
            { start := i3 }
        let s9 ← core.slice.Slice.fill core.clone.CloneU64 s8 0#u64
        let s10 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) s6
            { «end» := self.degree }
        let s11 := index_mut_back s9
        let b ←
          core.cmp.PartialEq.ne.trait_default
            (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU64) s10 s11
        if b
        then
          let o := get_or_insert_with_back basis1
          ok (core.result.Result.Ok (core.result.Result.Err
            types.DecodeFailure.NotSplit),
            { self with trace_len := i3, attempts := i },
            {
              buffers
                with
                trace := s11,
                gcd := s6,
                raw := s7,
                basis := { directions := o, len := basis_len1 }
            }, fun buffers1 => buffers1, meter2)
        else
          let o := get_or_insert_with_back basis1
          ok (core.result.Result.Ok (core.result.Result.Ok types.Stage.Gcd),
            { self with checked := true, trace_len := i3, attempts := i },
            {
              buffers
                with
                trace := s11,
                gcd := s6,
                raw := s7,
                basis := { directions := o, len := basis_len1 }
            }, fun buffers1 => buffers1, meter2)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result types.Stage types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        let o := get_or_insert_with_back basis1
        ok (r2, { self with trace_len := i3, attempts := i },
          {
            buffers
              with
              trace := s2,
              gcd := s3,
              raw := s4,
              basis := { directions := o, len := basis_len1 }
          }, fun buffers1 => buffers1, meter2)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (core.result.Result types.Stage types.DecodeFailure)
        (core.convert.FromSame types.DecodeError) residual
    ok (r1, self, buffers, fun buffers1 => buffers1, meter1)
end bulksketch
