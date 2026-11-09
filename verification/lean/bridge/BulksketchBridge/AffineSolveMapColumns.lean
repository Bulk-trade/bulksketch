import BulksketchBridge.AffineSolveMapSweep
import BulksketchBridge.AffineSolveMapTable
import BulksketchBridge.TimesXModSpec
import BulksketchBridge.PortableZipMap

namespace BulksketchBridge.AffineSolveMap

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.decode.affine bulksketch.backend.contract
open FrobeniusTables (entry read_normal)
open AffineSubspaces (iteratorAt)
open BulksketchBridge.MutableZip
open Algebra.Gf64

set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

abbrev Zip := BulksketchBridge.MutableZip.State U64 U64
abbrev Back := Zip → Zip

def addColumnWord (old row : U64) : U64 := old ^^^ row

theorem xor_zip (left right : Slice U64) (same : left.length = right.length)
    (start : Nat) (bound : start ≤ left.length) (back : Back) :
    ∃ restore, solve_map_loop0_loop0 (stateAt left right start) back =
      .ok (stateAt left right left.length, restore) ∧
      restore (stateAt left right left.length) =
        back (stateAt (mapFrom left right addColumnWord start) right left.length) := by
  suffices ∀ remaining start, start ≤ left.length → left.length - start = remaining →
    ∀ back : Back, ∃ restore, solve_map_loop0_loop0 (stateAt left right start) back =
      .ok (stateAt left right left.length, restore) ∧
      restore (stateAt left right left.length) =
        back (stateAt (mapFrom left right addColumnWord start) right left.length) by
    exact this (left.length - start) start bound rfl back
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro start bound measure back
    by_cases active : start < left.length
    · let nextBack := fun final => back (replaceLeft final start (addColumnWord left[start]! right[start]!))
      obtain ⟨restore, normal, behavior⟩ :=
        ih (left.length - (start + 1)) (by omega) (start + 1) (by omega) rfl nextBack
      have step :
          solve_map_loop0_loop0.body (stateAt left right start) back =
            .ok (.cont (stateAt left right (start + 1), nextBack)) := by
        have rightBound : start < right.length := by omega
        simp only [solve_map_loop0_loop0.body, next_some_at left right start active rightBound, bind_ok]
        dsimp! only
        rw [Slice.Inhabited_getElem_eq_getElem! left start active,
          Slice.Inhabited_getElem_eq_getElem! right start rightBound]
        simp only [lift, bind_ok, nextBack, addColumnWord]
      refine ⟨restore, ?_, ?_⟩
      · rw [solve_map_loop0_loop0, loop]
        dsimp only
        rw [step]
        simpa only [bind_ok, solve_map_loop0_loop0] using normal
      · rw [behavior]
        unfold nextBack
        rw [apply_step left right addColumnWord start active]
    · have endIndex : start = left.length := by omega
      subst start
      refine ⟨back, ?_, by rw [mapFrom_full_length]⟩
      rw [solve_map_loop0_loop0, loop]
      simp only [solve_map_loop0_loop0.body,
        next_done_at left right left.length (Or.inl (Nat.le_refl _)), bind_ok]
      dsimp! only
      simp only [bind_ok]

def columnTransform (coefficient old value : U64) : U64 :=
  if coefficient = 1#u64 then addColumnWord old value
  else old ^^^ (⟨multiplyWord coefficient.bv value.bv⟩ : U64)

def updateColumns (columns row : Columns) (coefficient : U64) : Columns :=
  if coefficient = 0#u64 then columns else
    Array.from_slice columns (mapFrom columns.to_slice row.to_slice (columnTransform coefficient) 0)

private theorem array_slice_length (columns : Columns) : columns.to_slice.length = 64 := by
  simp only [Array.to_slice, Slice.length, Slice.from_val, Array.property]
  rfl

private theorem array_zip (left right : Columns) :
    bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default
      (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
      (SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U64 64#usize)
      ⟨left.to_slice, 0⟩ right =
      .ok (stateAt left.to_slice right.to_slice 0, fun state => state.fst) := by
  simp only [bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default,
    Aeneas.Std.MutableZip.construct, SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_ok, stateAt, Array.to_slice]

private theorem scale_columns {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (scale : TimesXMod.ExactScaleXor kernels)
    (columns row : Columns) (coefficient : U64) (notOne : coefficient ≠ 1#u64) :
    kernels.ArithmeticInst.scale_xor columns.to_slice row.to_slice coefficient =
      .ok (mapFrom columns.to_slice row.to_slice (columnTransform coefficient) 0) := by
  have same : columns.to_slice.length = row.to_slice.length := by rw [array_slice_length, array_slice_length]
  obtain ⟨output, normal, length, word⟩ := scale columns.to_slice row.to_slice coefficient same
  rw [normal]
  apply congrArg Result.ok
  apply Slice.ext_getElem (length.trans (mapFrom_length _ _ _ _).symm)
  intro i leftBound rightBound
  have inside : i < columns.to_slice.length := by omega
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ leftBound, Slice.Inhabited_getElem_eq_getElem! _ _ rightBound,
    word i inside, mapFrom_word _ _ _ _ _ inside, ite_eq_left (Nat.zero_le _),
    columnTransform, ite_eq_right notOne]

/-- Native GF64 coefficient processing does not enter the small-field
fallback, and preserves the exact 64-column frame in every branch. -/
theorem gf64_columns_step {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64) (scale : TimesXMod.ExactScaleXor kernels)
    (table : Rows) (tableNormal : FROBENIUS_COLUMNS = .ok table)
    (linear : Slice U64) (index : Usize) (columns : Columns)
    (active : index.val < linear.length) (small : index.val < 64) :
    ∃ next, next.val = index.val + 1 ∧
      solve_map_loop0.body field kernels 64#u32 64#usize (iteratorAt linear index) columns =
        .ok (.cont (iteratorAt linear next, updateColumns columns (entry table index.val) linear[index.val]!)) := by
  obtain ⟨next, nextVal, forward⟩ := next_column linear index active small
  refine ⟨next, nextVal, ?_⟩
  let coefficient := linear[index.val]!
  let row := entry table index.val
  have bound : index.val < (64#usize).val := small
  have read := read_normal table index bound
  simp only [solve_map_loop0.body, forward, bind_ok]
  dsimp! only
  by_cases zero : coefficient = 0#u64
  · have zero' : linear[index.val]! = 0#u64 := zero
    simp only [zero', ite_true, updateColumns]
  · have zero' : linear[index.val]! ≠ 0#u64 := zero
    simp only [zero', ite_false, ite_true, tableNormal, bind_ok, read]
    by_cases one : coefficient = 1#u64
    · have one' : linear[index.val]! = 1#u64 := one
      have same : columns.to_slice.length = row.to_slice.length := by rw [array_slice_length, array_slice_length]
      obtain ⟨restore, normal, behavior⟩ :=
        xor_zip columns.to_slice row.to_slice same 0 (Nat.zero_le _) (fun z => z)
      dsimp only [row] at normal behavior
      simp only [one', ite_true, Array.to_slice_mut, lift, bind_ok]
      dsimp! only
      simp only [core.slice.Slice.iter_mut, bind_ok]
      dsimp! only
      simp only [array_zip, bind_ok]
      dsimp! only
      rw [normal]
      simp only [bind_ok]
      dsimp! only
      rw [behavior]
      rfl
    · have one' : linear[index.val]! ≠ 1#u64 := one
      simp only [one', ite_false, Array.to_slice_mut, lift, bind_ok]
      dsimp! only
      have exactScale := scale_columns kernels scale columns (entry table index.val) linear[index.val]! one'
      simp only [exactScale, bind_ok, updateColumns, zero', ite_false]

def foldColumns (linear : Slice U64) (table : Rows) (start : Nat) (columns : Columns) :
    Nat → Columns
  | 0 => columns
  | remaining + 1 => foldColumns linear table (start + 1)
      (updateColumns columns (entry table start) linear[start]!) remaining

theorem gf64_columns {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64) (scale : TimesXMod.ExactScaleXor kernels)
    (table : Rows) (tableNormal : FROBENIUS_COLUMNS = .ok table)
    (linear : Slice U64) (index : Usize) (columns : Columns)
    (small : linear.length ≤ 64) (within : index.val ≤ linear.length) :
    solve_map_loop0 field kernels 64#u32 (iteratorAt linear index) 64#usize columns =
      .ok (foldColumns linear table index.val columns (linear.length - index.val)) := by
  suffices ∀ (fuel : Nat) (index : Usize) (columns : Columns),
      index.val ≤ linear.length → linear.length - index.val = fuel →
      solve_map_loop0 field kernels 64#u32 (iteratorAt linear index) 64#usize columns =
        .ok (foldColumns linear table index.val columns fuel) by
    exact this _ index columns within rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro index columns within remaining
    by_cases active : index.val < linear.length
    · obtain ⟨next, nextVal, step⟩ :=
        gf64_columns_step field kernels scale table tableNormal linear index columns active (by omega)
      have continued := ih (linear.length - next.val) (by omega) next
        (updateColumns columns (entry table index.val) linear[index.val]!) (by omega) rfl
      have successor : fuel = (linear.length - next.val) + 1 := by omega
      rw [solve_map_loop0, loop]
      dsimp only
      rw [step]
      simp only [bind_ok]
      rw [successor, foldColumns]
      simpa only [solve_map_loop0, nextVal] using continued
    · have terminal : fuel = 0 := by omega
      rw [solve_map_loop0, loop, terminal, foldColumns]
      simp only [solve_map_loop0.body, no_column linear index (by omega), bind_ok]
      dsimp! only
      simp only [bind_ok]

#print axioms xor_zip
#print axioms gf64_columns_step
#print axioms gf64_columns

end BulksketchBridge.AffineSolveMap
