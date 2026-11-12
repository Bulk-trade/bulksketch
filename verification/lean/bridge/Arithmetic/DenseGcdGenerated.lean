-- Exact original Dense monic GCD and both loop declarations.
import Arithmetic.DenseExactDivideGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace Aeneas.Std.DenseGcdRuntime

/-- Both mutable slots are swapped in the forward direction, and the
returned pair is swapped back to the caller's original slot order. -/
def swapSlots {T : Type} (left right : T) : T × T × (T × T → T × T) :=
  (right, left, Prod.swap)

end Aeneas.Std.DenseGcdRuntime

namespace bulksketch

variable (division : DenseDivisionRuntime.DivRem)
local notation "poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into" => division
local notation "core.mem.swap" => DenseGcdRuntime.swapSlots

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::monic_gcd_into]: loop body 0:
    Source: 'src/poly/dense.rs', lines 129:8-141:9 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into_loop.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (back : Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → ((Slice
  Std.U64) × (Slice Std.U64) × (Slice Std.U64)))
  (raw : Slice types.RawProduct) (left : Slice Std.U64) (right : Slice Std.U64)
  (quotient : Slice Std.U64) (remainder : Slice Std.U64) (left_len : Std.Usize)
  (right_len : Std.Usize) :
  Result (ControlFlow ((Slice Std.U64 → Slice Std.U64 → Slice Std.U64 →
    ((Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64))) × (Slice
    types.RawProduct) × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64)
    × (Slice Std.U64) × Std.Usize × Std.Usize) ((Slice types.RawProduct) ×
    (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) ×
    Std.Usize × (Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → ((Slice
    Std.U64) × (Slice Std.U64) × (Slice Std.U64)))))
  := do
  if right_len != 0#usize
  then
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) left
        { «end» := left_len }
    let s1 ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) right
        { «end» := right_len }
    let ((_, len), quotient1, remainder1, raw1) ←
      poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into
        fieldBinaryFieldInst backendcontractBulkKernelsInst s s1 quotient
        remainder raw
    let (left1, right1, swap_back) := core.mem.swap left right
    let (right2, remainder2, swap_back1) := core.mem.swap right1 remainder1
    ok (cont
      (fun s2 s3 s4 =>
         let (s5, s6) := swap_back1 (s3, s4)
         let (s7, s8) := swap_back (s2, s5)
         back s7 s8 s6, raw1, left1, right2, quotient1, remainder2, right_len,
      len))
  else ok (done (raw, left, right, quotient, remainder, left_len, back))

local notation "poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into_loop.body" => (poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into_loop.body division)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::monic_gcd_into]: loop 0:
    Source: 'src/poly/dense.rs', lines 129:8-141:9 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into_loop
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (back : Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → ((Slice
  Std.U64) × (Slice Std.U64) × (Slice Std.U64)))
  (raw : Slice types.RawProduct) (left : Slice Std.U64) (right : Slice Std.U64)
  (quotient : Slice Std.U64) (remainder : Slice Std.U64) (left_len : Std.Usize)
  (right_len : Std.Usize) :
  Result ((Slice types.RawProduct) × (Slice Std.U64) × (Slice Std.U64) ×
    (Slice Std.U64) × (Slice Std.U64) × Std.Usize × (Slice Std.U64 → Slice
    Std.U64 → Slice Std.U64 → ((Slice Std.U64) × (Slice Std.U64) × (Slice
    Std.U64))))
  := do
  loop
    (fun (back1, raw1, left1, right1, quotient1, remainder1, left_len1,
      right_len1) =>
      poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into_loop.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst back1 raw1 left1
      right1 quotient1 remainder1 left_len1 right_len1)
    (back, raw, left, right, quotient, remainder, left_len, right_len)

local notation "poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into_loop" => (poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into_loop division)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::monic_gcd_into]:
    Source: 'src/poly/dense.rs', lines 113:4-153:5 -/
def poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (a : Slice Std.U64) (b : Slice Std.U64) (dst : Slice Std.U64)
  (work : Slice Std.U64) (raw : Slice types.RawProduct) :
  Result (Std.Usize × (Slice Std.U64) × (Slice Std.U64) × (Slice
    types.RawProduct))
  := do
  let i := Slice.len a
  let i1 := Slice.len b
  let max_len ← lift (core.cmp.impls.OrdUsize.max i i1)
  let width ← max_len + 1#usize
  let i2 := Slice.len dst
  massert (i2 >= max_len)
  let i3 := Slice.len work
  let i4 ← 4#usize * width
  massert (i3 >= i4)
  let i5 := Slice.len raw
  let i6 ← 2#usize * width
  massert (i5 >= i6)
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) work
      { «end» := i4 }
  let ((left, rest), split_at_mut_back) ←
    core.slice.Slice.split_at_mut s width
  let ((right, rest1), split_at_mut_back1) ←
    core.slice.Slice.split_at_mut rest width
  let ((quotient, remainder), split_at_mut_back2) ←
    core.slice.Slice.split_at_mut rest1 width
  let i7 := Slice.len a
  let (s1, index_mut_back1) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) left
      { «end» := i7 }
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s1 a
  let i8 := Slice.len b
  let (s3, index_mut_back2) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) right
      { «end» := i8 }
  let s4 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s3 b
  let left_len := Slice.len a
  let right_len := Slice.len b
  let right1 := index_mut_back2 s4
  let left1 := index_mut_back1 s2
  let (raw1, left2, right2, quotient1, remainder1, left_len1, back) ←
    poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into_loop
      fieldBinaryFieldInst backendcontractBulkKernelsInst
      (fun s5 s6 s7 => (s5, s6, s7)) raw left1 right1 quotient remainder
      left_len right_len
  let (s5, index_mut_back3) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) dst
      { «end» := max_len }
  let s6 ← core.slice.Slice.fill core.clone.CloneU64 s5 0#u64
  if left_len1 != 0#usize
  then
    let i9 ← left_len1 - 1#usize
    let i10 ← Slice.index_usize left2 i9
    if i10 = 1#u64
    then
      let dst1 := index_mut_back3 s6
      let (s7, index_mut_back4) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) dst1
          { «end» := left_len1 }
      let s8 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) left2
          { «end» := left_len1 }
      let s9 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s7 s8
      let dst2 := index_mut_back4 s9
      let (s10, s11, s12) := back left2 right2 remainder1
      let rest2 := split_at_mut_back2 (quotient1, s12)
      let rest3 := split_at_mut_back1 (s11, rest2)
      let s13 := split_at_mut_back (s10, rest3)
      let work1 := index_mut_back s13
      ok (left_len1, dst2, work1, raw1)
    else
      let i11 ← Slice.index_usize left2 i9
      let o ← backendcontractBulkKernelsInst.ArithmeticInst.inverse i11
      let inverse ←
        core.option.Option.expect o (toStr "nonzero gcd leading coefficient")
      let dst1 := index_mut_back3 s6
      let (s7, index_mut_back4) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) dst1
          { «end» := left_len1 }
      let s8 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) left2
          { «end» := left_len1 }
      let s9 ←
        backendcontractBulkKernelsInst.ArithmeticInst.scale_xor s7 s8 inverse
      let dst2 := index_mut_back4 s9
      let (s10, s11, s12) := back left2 right2 remainder1
      let rest2 := split_at_mut_back2 (quotient1, s12)
      let rest3 := split_at_mut_back1 (s11, rest2)
      let s13 := split_at_mut_back (s10, rest3)
      let work1 := index_mut_back s13
      ok (left_len1, dst2, work1, raw1)
  else
    let dst1 := index_mut_back3 s6
    let (s7, s8, s9) := back left2 right2 remainder1
    let rest2 := split_at_mut_back2 (quotient1, s9)
    let rest3 := split_at_mut_back1 (s8, rest2)
    let s10 := split_at_mut_back (s7, rest3)
    let work1 := index_mut_back s10
    ok (left_len1, dst1, work1, raw1)

end bulksketch
