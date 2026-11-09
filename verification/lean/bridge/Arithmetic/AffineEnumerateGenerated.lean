-- Exact selected original-affine enumeration declarations from checked extraction.
import Arithmetic.SliceKernelTypes
import Arithmetic.ReconstructionTypes
import Arithmetic.MutableZipRuntime
import Arithmetic.TrailingZeros

open Aeneas Aeneas.Std Result ControlFlow Error

namespace Aeneas.Std.MutableEnumerate

abbrev State (T : Type) := core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)

def construct {T : Type} (_ : MutableZip.LeftNext T) (iterator : core.slice.iter.IterMut T) :
    Result (State T × (State T → core.slice.iter.IterMut T)) :=
  .ok (⟨iterator, 0#usize⟩, fun state => state.iter)

def next {T : Type} (inner : MutableZip.LeftNext T) (state : State T) :
    Result (Option (Usize × T) × State T × (State T → Option (Usize × T) → State T)) := do
  let (item, advanced, restore) ← inner state.iter
  match item with
  | none =>
    .ok (none, { state with iter := advanced }, fun later _ =>
      { later with iter := restore later.iter none })
  | some value =>
    let count ← state.count + 1#usize
    .ok (some (state.count, value), ⟨advanced, count⟩, fun later replacement =>
      { later with iter := restore later.iter (replacement.map Prod.snd) })

def checkedShift (word : Usize) (amount : U32) : Result (Option Usize) :=
  .ok (if amount.val < System.Platform.numBits then some ⟨word.bv <<< amount.val⟩ else none)

end Aeneas.Std.MutableEnumerate

namespace bulksketch

set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

local notation "core.iter.adapters.enumerate.IteratorEnumerate.next" => Aeneas.Std.MutableEnumerate.next
local notation "core.iter.traits.iterator.Iterator.enumerate.trait_default" => Aeneas.Std.MutableEnumerate.construct
local notation "core.num.Usize.checked_shl" => Aeneas.Std.MutableEnumerate.checkedShift
local notation "core.iter.traits.iterator.Iterator.zip.trait_default" =>
  Aeneas.Std.core.iter.traits.iterator.Iterator.zip.trait_default
local notation "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next" =>
  Aeneas.Std.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next

/-- [bulksketch::decode::affine::enumerate]: loop body 1:
    Source: 'src/decode/affine.rs', lines 322:8-328:9 -/
@[rust_loop_body]
def decode.affine.enumerate_loop0_loop0.body
  (basis : Slice Std.U64) (start : Std.Usize)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  Std.U64))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  Std.U64) → core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  Std.U64)) (x : Std.U64) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut Std.U64)) ×
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut Std.U64)
    → core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    Std.U64)) × Std.U64) (Std.U64 × (core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut Std.U64)) ×
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut Std.U64)
    → core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    Std.U64))))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) iter
  match o with
  | none => ok (done (x, iter1, fun e => let e1 := next_back e none
                                         back e1))
  | some p =>
    let (offset, _) := p
    let index ← start + offset
    if index != 0#usize
    then
      let i ← core.num.Usize.trailing_zeros index
      let i1 ← lift (UScalar.cast .Usize i)
      let i2 ← Slice.index_usize basis i1
      let x1 ← lift (x ^^^ i2)
      ok (cont (iter1,
        fun e => let e1 := next_back e (some (offset, x1))
                 back e1, x1))
    else
      ok (cont (iter1,
        fun e => let e1 := next_back e (some (offset, x))
                 back e1, x))

/-- [bulksketch::decode::affine::enumerate]: loop 1:
    Source: 'src/decode/affine.rs', lines 322:8-328:9 -/
@[rust_loop]
def decode.affine.enumerate_loop0_loop0
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  Std.U64))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  Std.U64) → core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  Std.U64)) (basis : Slice Std.U64) (x : Std.U64) (start : Std.Usize) :
  Result (Std.U64 × (core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut Std.U64)) ×
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut Std.U64)
    → core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    Std.U64)))
  := do
  loop
    (fun (iter1, back1, x1) => decode.affine.enumerate_loop0_loop0.body basis
      start iter1 back1 x1)
    (iter, back, x)

/-- [bulksketch::decode::affine::enumerate]: loop body 2:
    Source: 'src/decode/affine.rs', lines 320:4-342:5 -/
@[rust_loop_body]
def decode.affine.enumerate_loop0_loop1.body
  (d : Std.Usize)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.Iter Std.U64)
  (core.slice.iter.Iter Std.U64)) (roots : Slice Std.U64) (found : Std.Usize) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.Iter
    Std.U64) (core.slice.iter.Iter Std.U64)) × (Slice Std.U64) × Std.Usize)
    (types.DecodeFailure × (Slice Std.U64) × Std.Usize × Bool))
  := do
  let (o, iter1) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64)
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (types.DecodeFailure.NotSplit, roots, found, true))
  | some p =>
    let (point, value) := p
    if value = 0#u64
    then
      if point = 0#u64
      then ok (done (types.DecodeFailure.InvalidLocator, roots, found, false))
      else
        if found = d
        then ok (done (types.DecodeFailure.NotSplit, roots, found, false))
        else
          let s ← Slice.update roots found point
          let found1 ← found + 1#usize
          ok (cont (iter1, s, found1))
    else ok (cont (iter1, roots, found))

/-- [bulksketch::decode::affine::enumerate]: loop 2:
    Source: 'src/decode/affine.rs', lines 320:4-342:5 -/
@[rust_loop]
def decode.affine.enumerate_loop0_loop1
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.Iter Std.U64)
  (core.slice.iter.Iter Std.U64)) (roots : Slice Std.U64) (d : Std.Usize)
  (found : Std.Usize) :
  Result (types.DecodeFailure × (Slice Std.U64) × Std.Usize × Bool)
  := do
  loop
    (fun (iter1, roots1, found1) => decode.affine.enumerate_loop0_loop1.body d
      iter1 roots1 found1)
    (iter, roots, found)

/-- [bulksketch::decode::affine::enumerate]: loop body 0:
    Source: 'src/decode/affine.rs', lines 320:4-347:1 -/
@[rust_loop_body]
def decode.affine.enumerate_loop0.body
  {F : Type _} {K : Type _} (backendcontractBulkKernelsInst :
  backend.contract.BulkKernels K F)
  (split_at_mut_back : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (polynomial : Slice Std.U64) (basis : Slice Std.U64) (d : Std.Usize)
  (batch : Std.Usize) (count : Std.Usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (roots : Slice Std.U64) (points : Slice Std.U64) (values : Slice Std.U64)
  (x : Std.U64) (found : Std.Usize) :
  Result (ControlFlow ((core.iter.adapters.step_by.StepBy (core.ops.range.Range
    Std.Usize)) × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) ×
    Std.U64 × Std.Usize) ((core.result.Result Std.Usize types.DecodeFailure)
    × (Slice Std.U64) × (Slice Std.U64)))
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none =>
    if found != d
    then
      let work := split_at_mut_back (points, values)
      ok (done (core.result.Result.Err types.DecodeFailure.NotSplit, roots,
        work))
    else
      let work := split_at_mut_back (points, values)
      ok (done (core.result.Result.Ok found, roots, work))
  | some start =>
    let i ← count - start
    let len ← lift (core.cmp.impls.OrdUsize.min batch i)
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) points
        { «end» := len }
    let (im, iter_mut_back) ← core.slice.Slice.iter_mut s
    let (iter2, trait_default_back) ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
        Std.U64) im
    let (x1, e, back) ←
      decode.affine.enumerate_loop0_loop0 iter2 (fun e1 => e1) basis x start
    let e1 := back e
    let im1 := trait_default_back e1
    let s1 := iter_mut_back im1
    let points1 := index_mut_back s1
    let s2 ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) points1
        { «end» := len }
    let (s3, index_mut_back1) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) values
        { «end» := len }
    let s4 ← backendcontractBulkKernelsInst.horner_many polynomial s2 s3
    let i1 ← core.slice.Slice.iter s2
    let values1 := index_mut_back1 s4
    let s5 ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) values1
        { «end» := len }
    let iter3 ←
      core.iter.traits.iterator.Iterator.zip.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.U64)
        (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter Std.U64)
        i1 s5
    let (df, roots1, found1, b) ←
      decode.affine.enumerate_loop0_loop1 iter3 roots d found
    if b
    then ok (cont (iter1, roots1, points1, values1, x1, found1))
    else
      let s6 := split_at_mut_back (points1, values1)
      ok (done (core.result.Result.Err df, roots1, s6))

/-- [bulksketch::decode::affine::enumerate]: loop 0:
    Source: 'src/decode/affine.rs', lines 320:4-347:1 -/
@[rust_loop]
def decode.affine.enumerate_loop0
  {F : Type _} {K : Type _} (backendcontractBulkKernelsInst :
  backend.contract.BulkKernels K F)
  (split_at_mut_back : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (polynomial : Slice Std.U64) (basis : Slice Std.U64) (roots : Slice Std.U64)
  (d : Std.Usize) (points : Slice Std.U64) (values : Slice Std.U64)
  (batch : Std.Usize) (count : Std.Usize) (x : Std.U64) (found : Std.Usize) :
  Result ((core.result.Result Std.Usize types.DecodeFailure) × (Slice Std.U64)
    × (Slice Std.U64))
  := do
  loop
    (fun (iter1, roots1, points1, values1, x1, found1) =>
      decode.affine.enumerate_loop0.body backendcontractBulkKernelsInst
      split_at_mut_back polynomial basis d batch count iter1 roots1 points1
      values1 x1 found1)
    (iter, roots, points, values, x, found)

/-- [bulksketch::decode::affine::enumerate]:
    Source: 'src/decode/affine.rs', lines 302:0-347:1 -/
def decode.affine.enumerate
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (polynomial : Slice Std.U64) (base : Std.U64) (basis : Slice Std.U64)
  (roots : Slice Std.U64) (work : Slice Std.U64) :
  Result ((core.result.Result Std.Usize types.DecodeFailure) × (Slice Std.U64)
    × (Slice Std.U64))
  := do
  let i := Slice.len polynomial
  let d ← i - 1#usize
  let i1 := Slice.len work
  let i2 ← i1 / 2#usize
  let ((points, values), split_at_mut_back) ←
    core.slice.Slice.split_at_mut work i2
  let i3 := Slice.len points
  let i4 := Slice.len values
  let batch ← lift (core.cmp.impls.OrdUsize.min i3 i4)
  let batch1 ←
    if batch >= 8#usize
    then do
         let i5 ← batch / 8#usize
         i5 * 8#usize
    else ok batch
  let i5 := Slice.len basis
  let i6 ← lift (UScalar.cast .U32 i5)
  let o ← core.num.Usize.checked_shl 1#usize i6
  let count ← core.option.Option.expect o (toStr "charged enumeration rank")
  let iter ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := count } batch1
  decode.affine.enumerate_loop0 backendcontractBulkKernelsInst
    split_at_mut_back iter polynomial basis roots d points values batch1 count
    base 0#usize
end bulksketch
