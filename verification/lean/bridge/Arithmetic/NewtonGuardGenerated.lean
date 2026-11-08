-- Exact original-source declaration projection. Imports are adapted only.
module
public import Arithmetic.SliceKernelTypes
public import Arithmetic.TrailingZeros
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

/-- [bulksketch::decode::deg34::guard]: loop body 2:
    Source: 'src/decode/deg34.rs', lines 53:12-55:13 -/
@[rust_loop_body]
def decode.deg34.guard_loop0_loop0_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.Range Std.U32) (observed : Std.U64) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × Std.U64) Std.U64)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done observed)
  | some _ =>
    let observed1 ←
      backendcontractBulkKernelsInst.ArithmeticInst.square observed
    ok (cont (iter1, observed1))

/-- [bulksketch::decode::deg34::guard]: loop 2:
    Source: 'src/decode/deg34.rs', lines 53:12-55:13 -/
@[rust_loop]
def decode.deg34.guard_loop0_loop0_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.Range Std.U32) (observed : Std.U64) :
  Result Std.U64
  := do
  loop
    (fun (iter1, observed1) => decode.deg34.guard_loop0_loop0_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter1 observed1)
    (iter, observed)

/-- [bulksketch::decode::deg34::guard]: loop body 1:
    Source: 'src/decode/deg34.rs', lines 49:8-57:9 -/
@[rust_loop_body]
def decode.deg34.guard_loop0_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (odd : Slice Std.U64) (degree : Std.Usize) (out : Slice Std.U64)
  (exponent : Std.Usize) (iter : core.ops.range.RangeInclusive Std.Usize)
  (residual : Std.U64) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.Usize) × Std.U64)
    Std.U64)
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter
  match o with
  | none => ok (done residual)
  | some lag =>
    let power ← exponent - lag
    let squares ← core.num.Usize.trailing_zeros power
    let i ← power >>> squares
    let i1 ← i / 2#usize
    let observed ← Slice.index_usize odd i1
    let observed1 ←
      decode.deg34.guard_loop0_loop0_loop0 fieldBinaryFieldInst
        backendcontractBulkKernelsInst { start := 0#u32, «end» := squares }
        observed
    let i2 ← degree - lag
    let i3 ← Slice.index_usize out i2
    let i4 ← backendcontractBulkKernelsInst.ArithmeticInst.mul i3 observed1
    let residual1 ← lift (residual ^^^ i4)
    ok (cont (iter1, residual1))

/-- [bulksketch::decode::deg34::guard]: loop 1:
    Source: 'src/decode/deg34.rs', lines 49:8-57:9 -/
@[rust_loop]
def decode.deg34.guard_loop0_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.RangeInclusive Std.Usize) (odd : Slice Std.U64)
  (degree : Std.Usize) (out : Slice Std.U64) (exponent : Std.Usize)
  (residual : Std.U64) :
  Result Std.U64
  := do
  loop
    (fun (iter1, residual1) => decode.deg34.guard_loop0_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst odd degree out
      exponent iter1 residual1)
    (iter, residual)

/-- [bulksketch::decode::deg34::guard]: loop body 0:
    Source: 'src/decode/deg34.rs', lines 44:4-63:1 -/
@[rust_loop_body]
def decode.deg34.guard_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (odd : Slice Std.U64) (degree : Std.Usize) (out : Slice Std.U64)
  (denominator : Std.U64) (iter : core.ops.range.Range Std.Usize) :
  Result (ControlFlow (core.ops.range.Range Std.Usize) Bool)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done true)
  | some index =>
    let i ← 2#usize * index
    let exponent ← i + 1#usize
    let i1 ← Slice.index_usize odd index
    let residual ←
      backendcontractBulkKernelsInst.ArithmeticInst.mul denominator i1
    let iter2 ← core.ops.range.RangeInclusive.new 1#usize degree
    let residual1 ←
      decode.deg34.guard_loop0_loop0 fieldBinaryFieldInst
        backendcontractBulkKernelsInst iter2 odd degree out exponent residual
    if residual1 != 0#u64
    then ok (done false)
    else ok (cont iter1)

/-- [bulksketch::decode::deg34::guard]: loop 0:
    Source: 'src/decode/deg34.rs', lines 44:4-63:1 -/
@[rust_loop]
def decode.deg34.guard_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.Range Std.Usize) (odd : Slice Std.U64)
  (degree : Std.Usize) (out : Slice Std.U64) (denominator : Std.U64) :
  Result Bool
  := do
  loop
    (fun iter1 => decode.deg34.guard_loop0.body fieldBinaryFieldInst
      backendcontractBulkKernelsInst odd degree out denominator iter1)
    iter

/-- [bulksketch::decode::deg34::guard]: loop body 5:
    Source: 'src/decode/deg34.rs', lines 53:12-55:13 -/
@[rust_loop_body]
def decode.deg34.guard_loop1_loop0_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.Range Std.U32) (observed : Std.U64) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × Std.U64) Std.U64)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done observed)
  | some _ =>
    let observed1 ←
      backendcontractBulkKernelsInst.ArithmeticInst.square observed
    ok (cont (iter1, observed1))

/-- [bulksketch::decode::deg34::guard]: loop 5:
    Source: 'src/decode/deg34.rs', lines 53:12-55:13 -/
@[rust_loop]
def decode.deg34.guard_loop1_loop0_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.Range Std.U32) (observed : Std.U64) :
  Result Std.U64
  := do
  loop
    (fun (iter1, observed1) => decode.deg34.guard_loop1_loop0_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter1 observed1)
    (iter, observed)

/-- [bulksketch::decode::deg34::guard]: loop body 4:
    Source: 'src/decode/deg34.rs', lines 49:8-57:9 -/
@[rust_loop_body]
def decode.deg34.guard_loop1_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (odd : Slice Std.U64) (degree : Std.Usize) (out : Slice Std.U64)
  (exponent : Std.Usize) (iter : core.ops.range.RangeInclusive Std.Usize)
  (residual : Std.U64) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.Usize) × Std.U64)
    Std.U64)
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter
  match o with
  | none => ok (done residual)
  | some lag =>
    let power ← exponent - lag
    let squares ← core.num.Usize.trailing_zeros power
    let i ← power >>> squares
    let i1 ← i / 2#usize
    let observed ← Slice.index_usize odd i1
    let observed1 ←
      decode.deg34.guard_loop1_loop0_loop0 fieldBinaryFieldInst
        backendcontractBulkKernelsInst { start := 0#u32, «end» := squares }
        observed
    let i2 ← degree - lag
    let i3 ← Slice.index_usize out i2
    let i4 ← backendcontractBulkKernelsInst.ArithmeticInst.mul i3 observed1
    let residual1 ← lift (residual ^^^ i4)
    ok (cont (iter1, residual1))

/-- [bulksketch::decode::deg34::guard]: loop 4:
    Source: 'src/decode/deg34.rs', lines 49:8-57:9 -/
@[rust_loop]
def decode.deg34.guard_loop1_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.RangeInclusive Std.Usize) (odd : Slice Std.U64)
  (degree : Std.Usize) (out : Slice Std.U64) (exponent : Std.Usize)
  (residual : Std.U64) :
  Result Std.U64
  := do
  loop
    (fun (iter1, residual1) => decode.deg34.guard_loop1_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst odd degree out
      exponent iter1 residual1)
    (iter, residual)

/-- [bulksketch::decode::deg34::guard]: loop body 3:
    Source: 'src/decode/deg34.rs', lines 44:4-63:1 -/
@[rust_loop_body]
def decode.deg34.guard_loop1.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (odd : Slice Std.U64) (degree : Std.Usize) (out : Slice Std.U64)
  (denominator : Std.U64) (iter : core.ops.range.Range Std.Usize) :
  Result (ControlFlow (core.ops.range.Range Std.Usize) Bool)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done true)
  | some index =>
    let i ← 2#usize * index
    let exponent ← i + 1#usize
    let i1 ← Slice.index_usize odd index
    let residual ←
      backendcontractBulkKernelsInst.ArithmeticInst.mul denominator i1
    let iter2 ← core.ops.range.RangeInclusive.new 1#usize degree
    let residual1 ←
      decode.deg34.guard_loop1_loop0 fieldBinaryFieldInst
        backendcontractBulkKernelsInst iter2 odd degree out exponent residual
    if residual1 != 0#u64
    then ok (done false)
    else ok (cont iter1)

/-- [bulksketch::decode::deg34::guard]: loop 3:
    Source: 'src/decode/deg34.rs', lines 44:4-63:1 -/
@[rust_loop]
def decode.deg34.guard_loop1
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.Range Std.Usize) (odd : Slice Std.U64)
  (degree : Std.Usize) (out : Slice Std.U64) (denominator : Std.U64) :
  Result Bool
  := do
  loop
    (fun iter1 => decode.deg34.guard_loop1.body fieldBinaryFieldInst
      backendcontractBulkKernelsInst odd degree out denominator iter1)
    iter

/-- [bulksketch::decode::deg34::guard]:
    Source: 'src/decode/deg34.rs', lines 10:0-63:1 -/
def decode.deg34.guard
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (odd : Slice Std.U64) (degree : Std.Usize) (out : Slice Std.U64) :
  Result (Bool × (Slice Std.U64))
  := do
  let s ← Slice.index_usize odd 0#usize
  let s2 ← backendcontractBulkKernelsInst.ArithmeticInst.square s
  let s4 ← backendcontractBulkKernelsInst.ArithmeticInst.square s2
  let i ← Slice.index_usize odd 1#usize
  let i1 ← backendcontractBulkKernelsInst.ArithmeticInst.mul s s2
  let a ← lift (i ^^^ i1)
  let i2 ← Slice.index_usize odd 2#usize
  let i3 ← backendcontractBulkKernelsInst.ArithmeticInst.mul i s2
  let b ← lift (i2 ^^^ i3)
  if degree = 3#usize
  then
    if a = 0#u64
    then ok (false, out)
    else
      let (s1, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) out
          { «end» := 5#usize }
      let i4 ← backendcontractBulkKernelsInst.ArithmeticInst.square a
      let i5 ← backendcontractBulkKernelsInst.ArithmeticInst.mul s b
      let i6 ← lift (i4 ^^^ i5)
      let i7 ← backendcontractBulkKernelsInst.ArithmeticInst.mul s a
      let s3 ←
        lift (Array.to_slice (Array.make 5#usize [ i6, b, i7, a, 0#u64 ]))
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s1 s3
      let out1 := index_mut_back s5
      let s6 ← Slice.update out1 5#usize a
      let i8 := Slice.len odd
      let i9 ← degree + 2#usize
      let i10 ← lift (core.cmp.impls.OrdUsize.min i8 i9)
      let b1 ←
        decode.deg34.guard_loop0 fieldBinaryFieldInst
          backendcontractBulkKernelsInst { start := degree, «end» := i10 }
          odd degree s6 a
      ok (b1, s6)
  else
    let i4 ← backendcontractBulkKernelsInst.ArithmeticInst.mul s s4
    let d ← lift (i2 ^^^ i4)
    let i5 ← Slice.index_usize odd 3#usize
    let i6 ← backendcontractBulkKernelsInst.ArithmeticInst.square i
    let i7 ← backendcontractBulkKernelsInst.ArithmeticInst.mul s i6
    let i8 ← lift (i5 ^^^ i7)
    let i9 ← backendcontractBulkKernelsInst.ArithmeticInst.mul a s4
    let c ← lift (i8 ^^^ i9)
    let i10 ← backendcontractBulkKernelsInst.ArithmeticInst.mul a i
    let i11 ← backendcontractBulkKernelsInst.ArithmeticInst.mul s d
    let denominator ← lift (i10 ^^^ i11)
    if denominator = 0#u64
    then ok (false, out)
    else
      let i12 ← backendcontractBulkKernelsInst.ArithmeticInst.mul b i
      let i13 ← backendcontractBulkKernelsInst.ArithmeticInst.mul s c
      let u2 ← lift (i12 ^^^ i13)
      let (s1, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) out
          { «end» := 5#usize }
      let i14 ← backendcontractBulkKernelsInst.ArithmeticInst.mul a c
      let i15 ← backendcontractBulkKernelsInst.ArithmeticInst.mul b d
      let i16 ← lift (i14 ^^^ i15)
      let i17 ←
        backendcontractBulkKernelsInst.ArithmeticInst.mul a denominator
      let i18 ← backendcontractBulkKernelsInst.ArithmeticInst.mul s u2
      let i19 ← lift (i17 ^^^ i18)
      let i20 ←
        backendcontractBulkKernelsInst.ArithmeticInst.mul s denominator
      let s3 ←
        lift (Array.to_slice
          (Array.make 5#usize [ i16, i19, u2, i20, denominator ]))
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s1 s3
      let out1 := index_mut_back s5
      let s6 ← Slice.update out1 5#usize denominator
      let i21 := Slice.len odd
      let i22 ← degree + 2#usize
      let i23 ← lift (core.cmp.impls.OrdUsize.min i21 i22)
      let b1 ←
        decode.deg34.guard_loop1 fieldBinaryFieldInst
          backendcontractBulkKernelsInst { start := degree, «end» := i23 }
          odd degree s6 denominator
      ok (b1, s6)

end bulksketch
