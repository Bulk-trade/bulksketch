-- Exact original locator declaration projection with scoped standard-library bindings.
import Arithmetic.WorkScheduleGenerated
import Arithmetic.ReconstructionTypes
import Arithmetic.RebuiltLfsrRuntime
import Arithmetic.PortableEncodingRuntime
import Arithmetic.DenseNormalizationGenerated
import Arithmetic.MutableZipRuntime
import Arithmetic.BmLocatorRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable section
namespace bulksketch

local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  Aeneas.Std.RebuiltLfsrRuntime.inclusive
local notation "core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  Aeneas.Std.BmLocatorRuntime.inclusiveRange
local notation "core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator" =>
  Aeneas.Std.BmLocatorRuntime.reverseIterator
/- The two original dictionary heads select existing shared and mutable
operations with their distinct Result shapes. This affects only this projection. -/
local macro "core.iter.traits.iterator.Iterator.zip.trait_default"
    leftDict:term:arg rightDict:term:arg left:term:arg input:term:arg : term =>
  match leftDict with
  | `((core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT $_)) =>
      `(Aeneas.Std.MutableZip.construct $rightDict $left $input)
  | `((core.iter.traits.iterator.IteratorSliceIter $_)) =>
      `(Aeneas.Std.core.iter.traits.iterator.Iterator.zip.trait_default
        $leftDict $rightDict $left $input)
  | _ => Lean.Macro.throwErrorAt leftDict "Unrecognized original BM Zip constructor dictionary"

local macro "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next"
    leftDict:term:arg rightDict:term:arg state:term:arg : term =>
  match leftDict with
  | `((core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT $_)) =>
      `(Aeneas.Std.MutableZip.next $leftDict $rightDict $state)
  | `((core.iter.traits.iterator.IteratorSliceIter $_)) =>
      `(Aeneas.Std.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
        $leftDict $rightDict $state)
  | _ => Lean.Macro.throwErrorAt leftDict "Unrecognized original BM Zip step dictionary"

/-- [bulksketch::decode::bm::locator]: loop body 1:
    Source: 'src/decode/bm.rs', lines 93:4-95:5 -/
@[rust_loop_body]
def decode.bm.locator_loop0_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (inverse : Std.U64) (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result (ControlFlow ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64))
    ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64 →
    core.slice.iter.IterMut Std.U64)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => let im1 := next_back im none
                                       back im1))
  | some coefficient =>
    let coefficient1 ←
      backendcontractBulkKernelsInst.ArithmeticInst.mul coefficient inverse
    ok (cont (iter1,
      fun im => let im1 := next_back im (some coefficient1)
                back im1))

/-- [bulksketch::decode::bm::locator]: loop 1:
    Source: 'src/decode/bm.rs', lines 93:4-95:5 -/
@[rust_loop]
def decode.bm.locator_loop0_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  (inverse : Std.U64) :
  Result ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64
    → core.slice.iter.IterMut Std.U64))
  := do
  loop
    (fun (iter1, back1) => decode.bm.locator_loop0_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst inverse iter1 back1)
    (iter, back)

/-- [bulksketch::decode::bm::locator]: loop body 2:
    Source: 'src/decode/bm.rs', lines 41:12-48:13 -/
@[rust_loop_body]
def decode.bm.locator_loop0_loop1.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.Iter Std.U64)
  (core.iter.adapters.rev.Rev (core.slice.iter.Iter Std.U64))) (i : Std.U64)
  (i1 : Std.U64) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.Iter
    Std.U64) (core.iter.adapters.rev.Rev (core.slice.iter.Iter Std.U64))) ×
    Std.U64 × Std.U64) (Std.U64 × Std.U64))
  := do
  let (o, iter1) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64)
      (core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator
      (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
      Std.U64)) iter
  match o with
  | none => ok (done (i, i1))
  | some p =>
    let (coefficient, syndrome) := p
    let term ←
      backendcontractBulkKernelsInst.ArithmeticInst.raw_mul coefficient
        syndrome
    let i2 ← lift (i ^^^ term.lo)
    let i3 ← lift (i1 ^^^ term.hi)
    ok (cont (iter1, i2, i3))

/-- [bulksketch::decode::bm::locator]: loop 2:
    Source: 'src/decode/bm.rs', lines 41:12-48:13 -/
@[rust_loop]
def decode.bm.locator_loop0_loop1
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.Iter Std.U64)
  (core.iter.adapters.rev.Rev (core.slice.iter.Iter Std.U64))) (i : Std.U64)
  (i1 : Std.U64) :
  Result (Std.U64 × Std.U64)
  := do
  loop
    (fun (iter1, i2, i3) => decode.bm.locator_loop0_loop1.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter1 i2 i3)
    (iter, i, i1)

/-- [bulksketch::decode::bm::locator]: loop body 3:
    Source: 'src/decode/bm.rs', lines 69:8-71:9 -/
@[rust_loop_body]
def decode.bm.locator_loop0_loop2.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (previous_delta : Std.U64) (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result (ControlFlow ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64))
    ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64 →
    core.slice.iter.IterMut Std.U64)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => let im1 := next_back im none
                                       back im1))
  | some coefficient =>
    let coefficient1 ←
      backendcontractBulkKernelsInst.ArithmeticInst.mul previous_delta
        coefficient
    ok (cont (iter1,
      fun im => let im1 := next_back im (some coefficient1)
                back im1))

/-- [bulksketch::decode::bm::locator]: loop 3:
    Source: 'src/decode/bm.rs', lines 69:8-71:9 -/
@[rust_loop]
def decode.bm.locator_loop0_loop2
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  (previous_delta : Std.U64) :
  Result ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64
    → core.slice.iter.IterMut Std.U64))
  := do
  loop
    (fun (iter1, back1) => decode.bm.locator_loop0_loop2.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst previous_delta iter1
      back1)
    (iter, back)

/-- [bulksketch::decode::bm::locator]: loop body 4:
    Source: 'src/decode/bm.rs', lines 73:8-78:9 -/
@[rust_loop_body]
def decode.bm.locator_loop0_loop3.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (delta : Std.U64)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    Std.U64) (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))) ((core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (iter1, fun z => let z1 := next_back z none
                                      back z1))
  | some p =>
    let (coefficient, old) := p
    let i ← backendcontractBulkKernelsInst.ArithmeticInst.mul delta old
    let coefficient1 ← lift (coefficient ^^^ i)
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (coefficient1, old))
               back z1))

/-- [bulksketch::decode::bm::locator]: loop 4:
    Source: 'src/decode/bm.rs', lines 73:8-78:9 -/
@[rust_loop]
def decode.bm.locator_loop0_loop3
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))
  (delta : Std.U64) :
  Result ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)))
  := do
  loop
    (fun (iter1, back1) => decode.bm.locator_loop0_loop3.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst delta iter1 back1)
    (iter, back)

/-- [bulksketch::decode::bm::locator]: loop body 5:
    Source: 'src/decode/bm.rs', lines 69:8-71:9 -/
@[rust_loop_body]
def decode.bm.locator_loop0_loop4.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (previous_delta : Std.U64) (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result (ControlFlow ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64))
    ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64 →
    core.slice.iter.IterMut Std.U64)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => let im1 := next_back im none
                                       back im1))
  | some coefficient =>
    let coefficient1 ←
      backendcontractBulkKernelsInst.ArithmeticInst.mul previous_delta
        coefficient
    ok (cont (iter1,
      fun im => let im1 := next_back im (some coefficient1)
                back im1))

/-- [bulksketch::decode::bm::locator]: loop 5:
    Source: 'src/decode/bm.rs', lines 69:8-71:9 -/
@[rust_loop]
def decode.bm.locator_loop0_loop4
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  (previous_delta : Std.U64) :
  Result ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64
    → core.slice.iter.IterMut Std.U64))
  := do
  loop
    (fun (iter1, back1) => decode.bm.locator_loop0_loop4.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst previous_delta iter1
      back1)
    (iter, back)

/-- [bulksketch::decode::bm::locator]: loop body 6:
    Source: 'src/decode/bm.rs', lines 73:8-78:9 -/
@[rust_loop_body]
def decode.bm.locator_loop0_loop5.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    Std.U64) (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))) ((core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (iter1, fun z => let z1 := next_back z none
                                      back z1))
  | some p =>
    let (coefficient, old) := p
    let i ← backendcontractBulkKernelsInst.ArithmeticInst.mul 0#u64 old
    let coefficient1 ← lift (coefficient ^^^ i)
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (coefficient1, old))
               back z1))

/-- [bulksketch::decode::bm::locator]: loop 6:
    Source: 'src/decode/bm.rs', lines 73:8-78:9 -/
@[rust_loop]
def decode.bm.locator_loop0_loop5
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)))
  := do
  loop
    (fun (iter1, back1) => decode.bm.locator_loop0_loop5.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter1 back1)
    (iter, back)

/-- [bulksketch::decode::bm::locator]: loop body 7:
    Source: 'src/decode/bm.rs', lines 41:12-48:13 -/
@[rust_loop_body]
def decode.bm.locator_loop0_loop6.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.Iter Std.U64)
  (core.iter.adapters.rev.Rev (core.slice.iter.Iter Std.U64))) (i : Std.U64)
  (i1 : Std.U64) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.Iter
    Std.U64) (core.iter.adapters.rev.Rev (core.slice.iter.Iter Std.U64))) ×
    Std.U64 × Std.U64) (Std.U64 × Std.U64))
  := do
  let (o, iter1) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64)
      (core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator
      (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
      Std.U64)) iter
  match o with
  | none => ok (done (i, i1))
  | some p =>
    let (coefficient, syndrome) := p
    let term ←
      backendcontractBulkKernelsInst.ArithmeticInst.raw_mul coefficient
        syndrome
    let i2 ← lift (i ^^^ term.lo)
    let i3 ← lift (i1 ^^^ term.hi)
    ok (cont (iter1, i2, i3))

/-- [bulksketch::decode::bm::locator]: loop 7:
    Source: 'src/decode/bm.rs', lines 41:12-48:13 -/
@[rust_loop]
def decode.bm.locator_loop0_loop6
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.Iter Std.U64)
  (core.iter.adapters.rev.Rev (core.slice.iter.Iter Std.U64))) (i : Std.U64)
  (i1 : Std.U64) :
  Result (Std.U64 × Std.U64)
  := do
  loop
    (fun (iter1, i2, i3) => decode.bm.locator_loop0_loop6.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter1 i2 i3)
    (iter, i, i1)

/-- [bulksketch::decode::bm::locator]: loop body 8:
    Source: 'src/decode/bm.rs', lines 69:8-71:9 -/
@[rust_loop_body]
def decode.bm.locator_loop0_loop7.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (previous_delta : Std.U64) (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result (ControlFlow ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64))
    ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64 →
    core.slice.iter.IterMut Std.U64)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => let im1 := next_back im none
                                       back im1))
  | some coefficient =>
    let coefficient1 ←
      backendcontractBulkKernelsInst.ArithmeticInst.mul previous_delta
        coefficient
    ok (cont (iter1,
      fun im => let im1 := next_back im (some coefficient1)
                back im1))

/-- [bulksketch::decode::bm::locator]: loop 8:
    Source: 'src/decode/bm.rs', lines 69:8-71:9 -/
@[rust_loop]
def decode.bm.locator_loop0_loop7
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  (previous_delta : Std.U64) :
  Result ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64
    → core.slice.iter.IterMut Std.U64))
  := do
  loop
    (fun (iter1, back1) => decode.bm.locator_loop0_loop7.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst previous_delta iter1
      back1)
    (iter, back)

/-- [bulksketch::decode::bm::locator]: loop body 9:
    Source: 'src/decode/bm.rs', lines 73:8-78:9 -/
@[rust_loop_body]
def decode.bm.locator_loop0_loop8.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (delta : Std.U64)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    Std.U64) (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))) ((core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (iter1, fun z => let z1 := next_back z none
                                      back z1))
  | some p =>
    let (coefficient, old) := p
    let i ← backendcontractBulkKernelsInst.ArithmeticInst.mul delta old
    let coefficient1 ← lift (coefficient ^^^ i)
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (coefficient1, old))
               back z1))

/-- [bulksketch::decode::bm::locator]: loop 9:
    Source: 'src/decode/bm.rs', lines 73:8-78:9 -/
@[rust_loop]
def decode.bm.locator_loop0_loop8
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))
  (delta : Std.U64) :
  Result ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)))
  := do
  loop
    (fun (iter1, back1) => decode.bm.locator_loop0_loop8.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst delta iter1 back1)
    (iter, back)

/-- [bulksketch::decode::bm::locator]: loop body 10:
    Source: 'src/decode/bm.rs', lines 69:8-71:9 -/
@[rust_loop_body]
def decode.bm.locator_loop0_loop9.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (previous_delta : Std.U64) (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result (ControlFlow ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64))
    ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64 →
    core.slice.iter.IterMut Std.U64)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => let im1 := next_back im none
                                       back im1))
  | some coefficient =>
    let coefficient1 ←
      backendcontractBulkKernelsInst.ArithmeticInst.mul previous_delta
        coefficient
    ok (cont (iter1,
      fun im => let im1 := next_back im (some coefficient1)
                back im1))

/-- [bulksketch::decode::bm::locator]: loop 10:
    Source: 'src/decode/bm.rs', lines 69:8-71:9 -/
@[rust_loop]
def decode.bm.locator_loop0_loop9
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  (previous_delta : Std.U64) :
  Result ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64
    → core.slice.iter.IterMut Std.U64))
  := do
  loop
    (fun (iter1, back1) => decode.bm.locator_loop0_loop9.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst previous_delta iter1
      back1)
    (iter, back)

/-- [bulksketch::decode::bm::locator]: loop body 11:
    Source: 'src/decode/bm.rs', lines 73:8-78:9 -/
@[rust_loop_body]
def decode.bm.locator_loop0_loop10.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    Std.U64) (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))) ((core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (iter1, fun z => let z1 := next_back z none
                                      back z1))
  | some p =>
    let (coefficient, old) := p
    let i ← backendcontractBulkKernelsInst.ArithmeticInst.mul 0#u64 old
    let coefficient1 ← lift (coefficient ^^^ i)
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (coefficient1, old))
               back z1))

/-- [bulksketch::decode::bm::locator]: loop 11:
    Source: 'src/decode/bm.rs', lines 73:8-78:9 -/
@[rust_loop]
def decode.bm.locator_loop0_loop10
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)))
  := do
  loop
    (fun (iter1, back1) => decode.bm.locator_loop0_loop10.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter1 back1)
    (iter, back)

/-- [bulksketch::decode::bm::locator]: loop body 0:
    Source: 'src/decode/bm.rs', lines 32:4-98:1 -/
@[rust_loop_body]
def decode.bm.locator_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (split_at_mut_back : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (split_at_mut_back1 : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (s : Slice Std.U64)
  (split_at_mut_back2 : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (syndromes : Slice Std.U64) (budget : Std.Usize) (cost : types.WorkUnits)
  (iter : core.ops.range.Range Std.Usize) (meter : types.WorkMeter)
  (connection : Slice Std.U64) (previous : Slice Std.U64)
  (saved : Slice Std.U64) (degree : Std.Usize) (previous_len : Std.Usize)
  (shift : Std.Usize) (previous_delta : Std.U64) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × types.WorkMeter ×
    (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) × Std.Usize ×
    Std.Usize × Std.Usize × Std.U64) ((core.result.Result (core.result.Result
    Std.Usize types.DecodeFailure) types.DecodeError) × (Slice Std.U64) ×
    types.WorkMeter))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let i ← Slice.index_usize connection degree
    if i = 0#u64
    then
      let rest := split_at_mut_back2 (saved, s)
      let rest1 := split_at_mut_back1 (previous, rest)
      let buffers := split_at_mut_back (connection, rest1)
      ok (done (core.result.Result.Ok (core.result.Result.Err
        types.DecodeFailure.InvalidLocator), buffers, meter))
    else
      let i1 ← Slice.index_usize connection 0#usize
      if i1 = 0#u64
      then
        let rest := split_at_mut_back2 (saved, s)
        let rest1 := split_at_mut_back1 (previous, rest)
        let buffers := split_at_mut_back (connection, rest1)
        ok (done (core.result.Result.Ok (core.result.Result.Err
          types.DecodeFailure.InvalidLocator), buffers, meter))
      else
        let o1 ← backendcontractBulkKernelsInst.ArithmeticInst.inverse i1
        let inverse ←
          core.option.Option.expect o1 (toStr "nonzero connection constant")
        let (s1, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
            Std.U64) connection { «end» := degree }
        let (iter2, into_iter_back) ←
          MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
            s1
        let (im, back) ←
          decode.bm.locator_loop0_loop0 fieldBinaryFieldInst
            backendcontractBulkKernelsInst iter2 (fun im1 => im1) inverse
        let im1 := back im
        let s2 := into_iter_back im1
        let connection1 := index_mut_back s2
        let (s3, index_mut_back1) ←
          core.slice.index.Slice.index_mut
            (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
            Std.U64) connection1 { «end» := degree }
        let s4 ← lift (core.slice.Slice.reverse s3)
        let connection2 := index_mut_back1 s4
        let rest := split_at_mut_back2 (saved, s)
        let rest1 := split_at_mut_back1 (previous, rest)
        let buffers := split_at_mut_back (connection2, rest1)
        ok (done (core.result.Result.Ok (core.result.Result.Ok degree),
          buffers, meter))
  | some n =>
    if n != 0#usize
    then
      let (r, meter1) ← types.WorkMeter.charge meter cost
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let b ← core.num.Usize.is_multiple_of n 2#usize
        if b
        then
          let s1 ←
            core.slice.index.Slice.index
              (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
              Std.U64) connection { «end» := degree }
          let i ← core.slice.Slice.iter s1
          let i1 ← n + 1#usize
          let i2 ← i1 - degree
          let ri ← core.ops.range.RangeInclusive.new i2 i1
          let s2 ←
            core.slice.index.Slice.index
              (core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
              Std.U64) syndromes ri
          let i3 ← core.slice.Slice.iter s2
          let r1 ←
            core.iter.traits.iterator.Iterator.rev.trait_default
              (core.iter.traits.iterator.IteratorSliceIter Std.U64)
              (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
              Std.U64) i3
          let iter2 ←
            core.iter.traits.iterator.Iterator.zip.trait_default
              (core.iter.traits.iterator.IteratorSliceIter Std.U64)
              (core.iter.traits.collect.IntoIterator.Blanket
              (core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator
              (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
              Std.U64))) i r1
          let (i4, i5) ←
            decode.bm.locator_loop0_loop1 fieldBinaryFieldInst
              backendcontractBulkKernelsInst iter2 0#u64 0#u64
          let delta ←
            backendcontractBulkKernelsInst.ArithmeticInst.reduce
              { lo := i4, hi := i5 }
          if delta = 0#u64
          then
            let shift1 ← shift + 1#usize
            ok (cont (iter1, meter1, connection, previous, saved, degree,
              previous_len, shift1, previous_delta))
          else
            let i6 ← 2#usize * degree
            let next_degree ←
              if i6 <= n
              then do
                   let i7 ← n + 1#usize
                   i7 - degree
              else ok degree
            if next_degree > budget
            then
              let rest := split_at_mut_back2 (saved, s)
              let rest1 := split_at_mut_back1 (previous, rest)
              let s3 := split_at_mut_back (connection, rest1)
              ok (done (core.result.Result.Ok (core.result.Result.Err
                types.DecodeFailure.DegreeExceedsBudget), s3, meter1))
            else
              let len ← degree + 1#usize
              let saved1 ←
                if i6 <= n
                then
                  do
                  let (s3, index_mut_back) ←
                    core.slice.index.Slice.index_mut
                      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                      saved { «end» := len }
                  let s4 ←
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                      connection { «end» := len }
                  let s5 ←
                    core.slice.Slice.copy_from_slice core.marker.CopyU64 s3 s4
                  ok (index_mut_back s5)
                else ok saved
              let (s3, index_mut_back) ←
                core.slice.index.Slice.index_mut
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                  connection { «end» := len }
              let (iter3, into_iter_back) ←
                MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
                  s3
              let (im, back) ←
                decode.bm.locator_loop0_loop2 fieldBinaryFieldInst
                  backendcontractBulkKernelsInst iter3 (fun im1 => im1)
                  previous_delta
              let im1 := back im
              let s4 := into_iter_back im1
              let connection1 := index_mut_back s4
              let ri1 ← core.ops.range.RangeInclusive.new len next_degree
              let (s5, index_mut_back1) ←
                core.slice.index.Slice.index_mut
                  (core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                  Std.U64) connection1 ri1
              let s6 ← core.slice.Slice.fill core.clone.CloneU64 s5 0#u64
              let connection2 := index_mut_back1 s6
              let i7 ← shift + previous_len
              let (s7, index_mut_back2) ←
                core.slice.index.Slice.index_mut
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U64)
                  connection2 { start := shift, «end» := i7 }
              let (im2, iter_mut_back) ← core.slice.Slice.iter_mut s7
              let s8 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                  previous { «end» := previous_len }
              let (iter4, trait_default_back) ←
                core.iter.traits.iterator.Iterator.zip.trait_default
                  (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
                  Std.U64)
                  (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
                  Std.U64) im2 s8
              let (z, back1) ←
                decode.bm.locator_loop0_loop3 fieldBinaryFieldInst
                  backendcontractBulkKernelsInst iter4 (fun z1 => z1) delta
              if i6 <= n
              then
                let (s9, index_mut_back3) ←
                  core.slice.index.Slice.index_mut
                    (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                    previous { «end» := len }
                let z1 := back1 z
                let im3 := trait_default_back z1
                let s10 := iter_mut_back im3
                let connection3 := index_mut_back2 s10
                let s11 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                    saved1 { «end» := len }
                let s12 ←
                  core.slice.Slice.copy_from_slice core.marker.CopyU64 s9 s11
                let previous1 := index_mut_back3 s12
                ok (cont (iter1, meter1, connection3, previous1, saved1,
                  next_degree, len, 1#usize, delta))
              else
                let shift1 ← shift + 1#usize
                let z1 := back1 z
                let im3 := trait_default_back z1
                let s9 := iter_mut_back im3
                let s10 := index_mut_back2 s9
                ok (cont (iter1, meter1, s10, previous, saved1, degree,
                  previous_len, shift1, previous_delta))
        else
          if 0#u64 = 0#u64
          then
            let shift1 ← shift + 1#usize
            ok (cont (iter1, meter1, connection, previous, saved, degree,
              previous_len, shift1, previous_delta))
          else
            let i ← 2#usize * degree
            let next_degree ←
              if i <= n
              then do
                   let i1 ← n + 1#usize
                   i1 - degree
              else ok degree
            if next_degree > budget
            then
              let rest := split_at_mut_back2 (saved, s)
              let rest1 := split_at_mut_back1 (previous, rest)
              let buffers := split_at_mut_back (connection, rest1)
              ok (done (core.result.Result.Ok (core.result.Result.Err
                types.DecodeFailure.DegreeExceedsBudget), buffers, meter1))
            else
              let len ← degree + 1#usize
              let saved1 ←
                if i <= n
                then
                  do
                  let (s1, index_mut_back) ←
                    core.slice.index.Slice.index_mut
                      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                      saved { «end» := len }
                  let s2 ←
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                      connection { «end» := len }
                  let s3 ←
                    core.slice.Slice.copy_from_slice core.marker.CopyU64 s1 s2
                  ok (index_mut_back s3)
                else ok saved
              let (s1, index_mut_back) ←
                core.slice.index.Slice.index_mut
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                  connection { «end» := len }
              let (iter2, into_iter_back) ←
                MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
                  s1
              let (im, back) ←
                decode.bm.locator_loop0_loop4 fieldBinaryFieldInst
                  backendcontractBulkKernelsInst iter2 (fun im1 => im1)
                  previous_delta
              let im1 := back im
              let s2 := into_iter_back im1
              let connection1 := index_mut_back s2
              let ri ← core.ops.range.RangeInclusive.new len next_degree
              let (s3, index_mut_back1) ←
                core.slice.index.Slice.index_mut
                  (core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                  Std.U64) connection1 ri
              let s4 ← core.slice.Slice.fill core.clone.CloneU64 s3 0#u64
              let connection2 := index_mut_back1 s4
              let i1 ← shift + previous_len
              let (s5, index_mut_back2) ←
                core.slice.index.Slice.index_mut
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U64)
                  connection2 { start := shift, «end» := i1 }
              let (im2, iter_mut_back) ← core.slice.Slice.iter_mut s5
              let s6 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                  previous { «end» := previous_len }
              let (iter3, trait_default_back) ←
                core.iter.traits.iterator.Iterator.zip.trait_default
                  (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
                  Std.U64)
                  (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
                  Std.U64) im2 s6
              let (z, back1) ←
                decode.bm.locator_loop0_loop5 fieldBinaryFieldInst
                  backendcontractBulkKernelsInst iter3 (fun z1 => z1)
              if i <= n
              then
                let (s7, index_mut_back3) ←
                  core.slice.index.Slice.index_mut
                    (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                    previous { «end» := len }
                let z1 := back1 z
                let im3 := trait_default_back z1
                let s8 := iter_mut_back im3
                let connection3 := index_mut_back2 s8
                let s9 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                    saved1 { «end» := len }
                let s10 ←
                  core.slice.Slice.copy_from_slice core.marker.CopyU64 s7 s9
                let previous1 := index_mut_back3 s10
                ok (cont (iter1, meter1, connection3, previous1, saved1,
                  next_degree, len, 1#usize, 0#u64))
              else
                let shift1 ← shift + 1#usize
                let z1 := back1 z
                let im3 := trait_default_back z1
                let s7 := iter_mut_back im3
                let s8 := index_mut_back2 s7
                ok (cont (iter1, meter1, s8, previous, saved1, degree,
                  previous_len, shift1, previous_delta))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result Std.Usize types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        let rest := split_at_mut_back2 (saved, s)
        let rest1 := split_at_mut_back1 (previous, rest)
        let buffers := split_at_mut_back (connection, rest1)
        ok (done (r1, buffers, meter1))
    else
      let b ← core.num.Usize.is_multiple_of n 2#usize
      if b
      then
        let s1 ←
          core.slice.index.Slice.index
            (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
            Std.U64) connection { «end» := degree }
        let i ← core.slice.Slice.iter s1
        let i1 ← n + 1#usize
        let i2 ← i1 - degree
        let ri ← core.ops.range.RangeInclusive.new i2 i1
        let s2 ←
          core.slice.index.Slice.index
            (core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
            Std.U64) syndromes ri
        let i3 ← core.slice.Slice.iter s2
        let r ←
          core.iter.traits.iterator.Iterator.rev.trait_default
            (core.iter.traits.iterator.IteratorSliceIter Std.U64)
            (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
            Std.U64) i3
        let iter2 ←
          core.iter.traits.iterator.Iterator.zip.trait_default
            (core.iter.traits.iterator.IteratorSliceIter Std.U64)
            (core.iter.traits.collect.IntoIterator.Blanket
            (core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator
            (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
            Std.U64))) i r
        let (i4, i5) ←
          decode.bm.locator_loop0_loop6 fieldBinaryFieldInst
            backendcontractBulkKernelsInst iter2 0#u64 0#u64
        let delta ←
          backendcontractBulkKernelsInst.ArithmeticInst.reduce
            { lo := i4, hi := i5 }
        if delta = 0#u64
        then
          let shift1 ← shift + 1#usize
          ok (cont (iter1, meter, connection, previous, saved, degree,
            previous_len, shift1, previous_delta))
        else
          let i6 ← 2#usize * degree
          let next_degree ←
            if i6 <= n
            then do
                 let i7 ← n + 1#usize
                 i7 - degree
            else ok degree
          if next_degree > budget
          then
            let rest := split_at_mut_back2 (saved, s)
            let rest1 := split_at_mut_back1 (previous, rest)
            let s3 := split_at_mut_back (connection, rest1)
            ok (done (core.result.Result.Ok (core.result.Result.Err
              types.DecodeFailure.DegreeExceedsBudget), s3, meter))
          else
            let len ← degree + 1#usize
            let saved1 ←
              if i6 <= n
              then
                do
                let (s3, index_mut_back) ←
                  core.slice.index.Slice.index_mut
                    (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                    saved { «end» := len }
                let s4 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                    connection { «end» := len }
                let s5 ←
                  core.slice.Slice.copy_from_slice core.marker.CopyU64 s3 s4
                ok (index_mut_back s5)
              else ok saved
            let (s3, index_mut_back) ←
              core.slice.index.Slice.index_mut
                (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                connection { «end» := len }
            let (iter3, into_iter_back) ←
              MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
                s3
            let (im, back) ←
              decode.bm.locator_loop0_loop7 fieldBinaryFieldInst
                backendcontractBulkKernelsInst iter3 (fun im1 => im1)
                previous_delta
            let im1 := back im
            let s4 := into_iter_back im1
            let connection1 := index_mut_back s4
            let ri1 ← core.ops.range.RangeInclusive.new len next_degree
            let (s5, index_mut_back1) ←
              core.slice.index.Slice.index_mut
                (core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                Std.U64) connection1 ri1
            let s6 ← core.slice.Slice.fill core.clone.CloneU64 s5 0#u64
            let connection2 := index_mut_back1 s6
            let i7 ← shift + previous_len
            let (s7, index_mut_back2) ←
              core.slice.index.Slice.index_mut
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U64)
                connection2 { start := shift, «end» := i7 }
            let (im2, iter_mut_back) ← core.slice.Slice.iter_mut s7
            let s8 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) previous
                { «end» := previous_len }
            let (iter4, trait_default_back) ←
              core.iter.traits.iterator.Iterator.zip.trait_default
                (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
                Std.U64)
                (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
                Std.U64) im2 s8
            let (z, back1) ←
              decode.bm.locator_loop0_loop8 fieldBinaryFieldInst
                backendcontractBulkKernelsInst iter4 (fun z1 => z1) delta
            if i6 <= n
            then
              let (s9, index_mut_back3) ←
                core.slice.index.Slice.index_mut
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                  previous { «end» := len }
              let z1 := back1 z
              let im3 := trait_default_back z1
              let s10 := iter_mut_back im3
              let connection3 := index_mut_back2 s10
              let s11 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) saved1
                  { «end» := len }
              let s12 ←
                core.slice.Slice.copy_from_slice core.marker.CopyU64 s9 s11
              let previous1 := index_mut_back3 s12
              ok (cont (iter1, meter, connection3, previous1, saved1,
                next_degree, len, 1#usize, delta))
            else
              let shift1 ← shift + 1#usize
              let z1 := back1 z
              let im3 := trait_default_back z1
              let s9 := iter_mut_back im3
              let s10 := index_mut_back2 s9
              ok (cont (iter1, meter, s10, previous, saved1, degree,
                previous_len, shift1, previous_delta))
      else
        if 0#u64 = 0#u64
        then
          let shift1 ← shift + 1#usize
          ok (cont (iter1, meter, connection, previous, saved, degree,
            previous_len, shift1, previous_delta))
        else
          let i ← 2#usize * degree
          let next_degree ←
            if i <= n
            then do
                 let i1 ← n + 1#usize
                 i1 - degree
            else ok degree
          if next_degree > budget
          then
            let rest := split_at_mut_back2 (saved, s)
            let rest1 := split_at_mut_back1 (previous, rest)
            let buffers := split_at_mut_back (connection, rest1)
            ok (done (core.result.Result.Ok (core.result.Result.Err
              types.DecodeFailure.DegreeExceedsBudget), buffers, meter))
          else
            let len ← degree + 1#usize
            let saved1 ←
              if i <= n
              then
                do
                let (s1, index_mut_back) ←
                  core.slice.index.Slice.index_mut
                    (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                    saved { «end» := len }
                let s2 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                    connection { «end» := len }
                let s3 ←
                  core.slice.Slice.copy_from_slice core.marker.CopyU64 s1 s2
                ok (index_mut_back s3)
              else ok saved
            let (s1, index_mut_back) ←
              core.slice.index.Slice.index_mut
                (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                connection { «end» := len }
            let (iter2, into_iter_back) ←
              MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
                s1
            let (im, back) ←
              decode.bm.locator_loop0_loop9 fieldBinaryFieldInst
                backendcontractBulkKernelsInst iter2 (fun im1 => im1)
                previous_delta
            let im1 := back im
            let s2 := into_iter_back im1
            let connection1 := index_mut_back s2
            let ri ← core.ops.range.RangeInclusive.new len next_degree
            let (s3, index_mut_back1) ←
              core.slice.index.Slice.index_mut
                (core.ops.range.RangeInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                Std.U64) connection1 ri
            let s4 ← core.slice.Slice.fill core.clone.CloneU64 s3 0#u64
            let connection2 := index_mut_back1 s4
            let i1 ← shift + previous_len
            let (s5, index_mut_back2) ←
              core.slice.index.Slice.index_mut
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U64)
                connection2 { start := shift, «end» := i1 }
            let (im2, iter_mut_back) ← core.slice.Slice.iter_mut s5
            let s6 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) previous
                { «end» := previous_len }
            let (iter3, trait_default_back) ←
              core.iter.traits.iterator.Iterator.zip.trait_default
                (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
                Std.U64)
                (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
                Std.U64) im2 s6
            let (z, back1) ←
              decode.bm.locator_loop0_loop10 fieldBinaryFieldInst
                backendcontractBulkKernelsInst iter3 (fun z1 => z1)
            if i <= n
            then
              let (s7, index_mut_back3) ←
                core.slice.index.Slice.index_mut
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                  previous { «end» := len }
              let z1 := back1 z
              let im3 := trait_default_back z1
              let s8 := iter_mut_back im3
              let connection3 := index_mut_back2 s8
              let s9 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) saved1
                  { «end» := len }
              let s10 ←
                core.slice.Slice.copy_from_slice core.marker.CopyU64 s7 s9
              let previous1 := index_mut_back3 s10
              ok (cont (iter1, meter, connection3, previous1, saved1,
                next_degree, len, 1#usize, 0#u64))
            else
              let shift1 ← shift + 1#usize
              let z1 := back1 z
              let im3 := trait_default_back z1
              let s7 := iter_mut_back im3
              let s8 := index_mut_back2 s7
              ok (cont (iter1, meter, s8, previous, saved1, degree,
                previous_len, shift1, previous_delta))

/-- [bulksketch::decode::bm::locator]: loop 0:
    Source: 'src/decode/bm.rs', lines 32:4-98:1 -/
@[rust_loop]
def decode.bm.locator_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (split_at_mut_back : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (split_at_mut_back1 : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (s : Slice Std.U64)
  (split_at_mut_back2 : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (iter : core.ops.range.Range Std.Usize) (syndromes : Slice Std.U64)
  (budget : Std.Usize) (meter : types.WorkMeter) (cost : types.WorkUnits)
  (connection : Slice Std.U64) (previous : Slice Std.U64)
  (saved : Slice Std.U64) (degree : Std.Usize) (previous_len : Std.Usize)
  (shift : Std.Usize) (previous_delta : Std.U64) :
  Result ((core.result.Result (core.result.Result Std.Usize
    types.DecodeFailure) types.DecodeError) × (Slice Std.U64) ×
    types.WorkMeter)
  := do
  loop
    (fun (iter1, meter1, connection1, previous1, saved1, degree1,
      previous_len1, shift1, previous_delta1) => decode.bm.locator_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst split_at_mut_back
      split_at_mut_back1 s split_at_mut_back2 syndromes budget cost iter1
      meter1 connection1 previous1 saved1 degree1 previous_len1 shift1
      previous_delta1)
    (iter, meter, connection, previous, saved, degree, previous_len, shift,
      previous_delta)

/-- [bulksketch::decode::bm::locator]:
    Source: 'src/decode/bm.rs', lines 14:0-98:1 -/
def decode.bm.locator
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (syndromes : Slice Std.U64) (capacity : Std.Usize) (budget : Std.Usize)
  (buffers : Slice Std.U64) (meter : types.WorkMeter) :
  Result ((core.result.Result (core.result.Result Std.Usize
    types.DecodeFailure) types.DecodeError) × (Slice Std.U64) ×
    types.WorkMeter)
  := do
  let r ← decode.work.WorkScheduleV1.cost (decode.work.Charge.BmStep budget)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r1, meter1) ← types.WorkMeter.charge meter val
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let width ← capacity + 1#usize
      let ((connection, rest), split_at_mut_back) ←
        core.slice.Slice.split_at_mut buffers width
      let ((previous, rest1), split_at_mut_back1) ←
        core.slice.Slice.split_at_mut rest width
      let ((saved, s), split_at_mut_back2) ←
        core.slice.Slice.split_at_mut rest1 width
      let (s1, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
          Std.U64) connection { «end» := budget }
      let s2 ← core.slice.Slice.fill core.clone.CloneU64 s1 0#u64
      let (s3, index_mut_back1) ←
        core.slice.index.Slice.index_mut
          (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
          Std.U64) previous { «end» := budget }
      let s4 ← core.slice.Slice.fill core.clone.CloneU64 s3 0#u64
      let connection1 := index_mut_back s2
      let s5 ← Slice.update connection1 0#usize 1#u64
      let previous1 := index_mut_back1 s4
      let s6 ← Slice.update previous1 0#usize 1#u64
      let i ← 2#usize * capacity
      decode.bm.locator_loop0 fieldBinaryFieldInst
        backendcontractBulkKernelsInst split_at_mut_back split_at_mut_back1 s
        split_at_mut_back2 { start := 0#usize, «end» := i } syndromes budget
        meter1 val s5 s6 saved 0#usize 1#usize 1#usize 1#u64
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (core.result.Result Std.Usize types.DecodeFailure)
          (core.convert.FromSame types.DecodeError) residual
      ok (r2, buffers, meter1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (core.result.Result Std.Usize types.DecodeFailure)
        (core.convert.FromSame types.DecodeError) residual
    ok (r1, buffers, meter)

end bulksketch
