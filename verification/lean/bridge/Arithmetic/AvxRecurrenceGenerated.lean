-- Original stock checked AVX continuation with exact selected runtime bindings.
import Arithmetic.AvxSquareRuntime
import Arithmetic.X86LaneMaskGenerated
import BulksketchBridge.X86MaskedMemoryRegister

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Aeneas.Std.AvxRecurrenceRuntime

open Avx512Register BulksketchBridge.X86MaskedMemory

def laneTest (left right : Word512) (lane : Fin 8) : Bool :=
  decide (flatten left lane &&& flatten right lane ≠ 0)

def testMask (left right : Word512) : Result U8 :=
  .ok ⟨BitVec.cast (by simp) (BitVec.ofBoolListLE (List.ofFn (laneTest left right)))⟩

end Aeneas.Std.AvxRecurrenceRuntime

namespace bulksketch

variable (loadModel : AvxSquareRuntime.Load)
local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "backend.x86_vpclmul512.load" => loadModel
local notation "core.core_arch.x86.avx512f._mm512_setzero_si512" => AvxSquareRuntime.zero
local notation "core.core_arch.x86.avx512f._mm512_set1_epi64" => Avx512Register.broadcast
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "core.core_arch.x86.avx512f._mm512_unpacklo_epi64" => Avx512Register.unpack false
local notation "core.core_arch.x86.avx512f._mm512_test_epi64_mask" => AvxRecurrenceRuntime.testMask
local notation "core.num.U64.to_ne_bytes" => X86PclmulRuntime.unsignedBytes
local notation "core.num.I64.from_ne_bytes" => X86PclmulRuntime.signedFromBytes

/-- [bulksketch::backend::x86_vpclmul512::odd_recurrence_matches]: loop body 1:
    Source: 'src/backend/x86_vpclmul512.rs', lines 842:8-849:9 -/
@[rust_loop_body]
def backend.x86_vpclmul512.odd_recurrence_matches_loop0_loop0.body
  (odd : Slice Std.U64) (squared_locator : Slice Std.U64) (index : Std.Usize)
  (len : Std.Usize) (iter : core.ops.range.RangeInclusive Std.Usize)
  (even : core.core_arch.x86.__m512i) (high : core.core_arch.x86.__m512i) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.Usize) ×
    core.core_arch.x86.__m512i × core.core_arch.x86.__m512i)
    (core.core_arch.x86.__m512i × core.core_arch.x86.__m512i))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter
  match o with
  | none => ok (done (even, high))
  | some lag =>
    let i ← index - lag
    let i1 ← i + len
    let s ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U64) odd { start := i, «end» := i1 }
    let mi ← backend.x86_vpclmul512.load s
    let i2 ← Slice.index_usize squared_locator lag
    let a ← core.num.U64.to_ne_bytes i2
    let i3 ← core.num.I64.from_ne_bytes a
    let mi1 ← core.core_arch.x86.avx512f._mm512_set1_epi64 i3
    let (low, upper) ← backend.x86_vpclmul512.raw mi mi1
    let even1 ← core.core_arch.x86.avx512f._mm512_xor_si512 even low
    let high1 ← core.core_arch.x86.avx512f._mm512_xor_si512 high upper
    ok (cont (iter1, even1, high1))

local notation "backend.x86_vpclmul512.odd_recurrence_matches_loop0_loop0.body" => (backend.x86_vpclmul512.odd_recurrence_matches_loop0_loop0.body loadModel)

/-- [bulksketch::backend::x86_vpclmul512::odd_recurrence_matches]: loop 1:
    Source: 'src/backend/x86_vpclmul512.rs', lines 842:8-849:9 -/
@[rust_loop]
def backend.x86_vpclmul512.odd_recurrence_matches_loop0_loop0
  (iter : core.ops.range.RangeInclusive Std.Usize) (odd : Slice Std.U64)
  (squared_locator : Slice Std.U64) (index : Std.Usize) (len : Std.Usize)
  (even : core.core_arch.x86.__m512i) (high : core.core_arch.x86.__m512i) :
  Result (core.core_arch.x86.__m512i × core.core_arch.x86.__m512i)
  := do
  loop
    (fun (iter1, even1, high1) =>
      backend.x86_vpclmul512.odd_recurrence_matches_loop0_loop0.body odd
      squared_locator index len iter1 even1 high1)
    (iter, even, high)

local notation "backend.x86_vpclmul512.odd_recurrence_matches_loop0_loop0" => (backend.x86_vpclmul512.odd_recurrence_matches_loop0_loop0 loadModel)

/-- [bulksketch::backend::x86_vpclmul512::odd_recurrence_matches]: loop body 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 838:4-857:1 -/
@[rust_loop_body]
def backend.x86_vpclmul512.odd_recurrence_matches_loop0.body
  (odd : Slice Std.U64) (squared_locator : Slice Std.U64) (degree : Std.Usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize)) :
  Result (ControlFlow (core.iter.adapters.step_by.StepBy (core.ops.range.Range
    Std.Usize)) Bool)
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done true)
  | some index =>
    let i := Slice.len odd
    let i1 ← i - index
    let len ← lift (core.cmp.impls.OrdUsize.min i1 8#usize)
    let even ← core.core_arch.x86.avx512f._mm512_setzero_si512
    let iter2 ← core.ops.range.RangeInclusive.new 1#usize degree
    let (even1, high) ←
      backend.x86_vpclmul512.odd_recurrence_matches_loop0_loop0 iter2 odd
        squared_locator index len even even
    let mi ← backend.x86_vpclmul512.reduce_cl even1
    let mi1 ← backend.x86_vpclmul512.reduce_cl high
    let expected ← core.core_arch.x86.avx512f._mm512_unpacklo_epi64 mi mi1
    let i2 ← index + len
    let s ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U64) odd { start := index, «end» := i2 }
    let mi2 ← backend.x86_vpclmul512.load s
    let mismatch ← core.core_arch.x86.avx512f._mm512_xor_si512 expected mi2
    let mi3 ← core.core_arch.x86.avx512f._mm512_set1_epi64 (-1)#i64
    let i3 ← core.core_arch.x86.avx512f._mm512_test_epi64_mask mismatch mi3
    let i4 ← backend.x86_vpclmul512.mask len
    let i5 ← lift (i3 &&& i4)
    if i5 != 0#u8
    then ok (done false)
    else ok (cont iter1)

local notation "backend.x86_vpclmul512.odd_recurrence_matches_loop0.body" => (backend.x86_vpclmul512.odd_recurrence_matches_loop0.body loadModel)

/-- [bulksketch::backend::x86_vpclmul512::odd_recurrence_matches]: loop 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 838:4-857:1 -/
@[rust_loop]
def backend.x86_vpclmul512.odd_recurrence_matches_loop0
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (odd : Slice Std.U64) (squared_locator : Slice Std.U64) (degree : Std.Usize)
  :
  Result Bool
  := do
  loop
    (fun iter1 => backend.x86_vpclmul512.odd_recurrence_matches_loop0.body odd
      squared_locator degree iter1)
    iter

local notation "backend.x86_vpclmul512.odd_recurrence_matches_loop0" => (backend.x86_vpclmul512.odd_recurrence_matches_loop0 loadModel)

/-- [bulksketch::backend::x86_vpclmul512::odd_recurrence_matches]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 836:0-857:1 -/
def backend.x86_vpclmul512.odd_recurrence_matches
  (odd : Slice Std.U64) (squared_locator : Slice Std.U64) : Result Bool := do
  let i := Slice.len squared_locator
  let degree ← i - 1#usize
  let i1 := Slice.len odd
  let iter ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := degree, «end» := i1 } 8#usize
  backend.x86_vpclmul512.odd_recurrence_matches_loop0 iter odd squared_locator
    degree

end bulksketch
