import BulksketchBridge.DenseReducerAlgebra
import BulksketchBridge.DenseReducerTable

namespace BulksketchBridge.DenseReducerTable

open Aeneas.Std DenseReducerAlgebra DenseCoefficient SliceKernels TimesXMod
open bulksketch.backend.contract

set_option maxRecDepth 4096

private theorem row_read (table : Slice U64) (degree row i : Nat)
    (bounded : (row + 1) * degree ≤ table.length) (inside : i < degree) :
    (tableRow table degree row)[i]! = table[row * degree + i]! := by
  simp only [tableRow, ClosedLeaf.region, Slice.getElem!_Nat_eq, Slice.from_val]
  apply List.getElem!_slice
  refine ⟨bounded, ?_⟩
  rw [Nat.add_mul]
  omega

private theorem row_size (table : Slice U64) (degree row : Nat)
    (bounded : (row + 1) * degree ≤ table.length) :
    (tableRow table degree row).length = degree := by
  rw [tableRow, ClosedLeaf.region_length _ _ _ bounded, Nat.add_mul]
  omega

private theorem read_written (table current : Slice U64) (degree row : Nat)
    (currentLen : current.length = degree) (bounded : (row + 1) * degree ≤ table.length) :
    tableRow (table.setSlice! (row * degree) current.val) degree row = current := by
  have updatedBound : (row + 1) * degree ≤ (table.setSlice! (row * degree) current.val).length := by
    rwa [Slice.setSlice!_length]
  apply Slice.ext_getElem ((row_size _ _ _ updatedBound).trans currentLen.symm)
  intro i newBound oldBound
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ newBound,
    Slice.Inhabited_getElem_eq_getElem! _ _ oldBound, row_read _ _ _ _ updatedBound (by omega)]
  simp only [Slice.getElem!_Nat_eq, Slice.setSlice!_val]
  have endValue : (row + 1) * degree = row * degree + degree := by rw [Nat.add_mul, Nat.one_mul]
  rw [List.getElem!_setSlice!_middle _ _ _ _ (by change _ ∧ _ < current.length ∧ _ < table.length; omega),
    Nat.add_sub_cancel_left]

private theorem read_before (table current : Slice U64) (degree row earlier : Nat)
    (earlierRow : earlier < row) (bounded : row * degree ≤ table.length) :
    tableRow (table.setSlice! (row * degree) current.val) degree earlier = tableRow table degree earlier := by
  have stop : (earlier + 1) * degree ≤ row * degree := Nat.mul_le_mul_right _ (by omega)
  have oldBound := stop.trans bounded
  have newBound : (earlier + 1) * degree ≤ (table.setSlice! (row * degree) current.val).length := by
    rwa [Slice.setSlice!_length]
  apply Slice.ext_getElem ((row_size _ _ _ newBound).trans (row_size _ _ _ oldBound).symm)
  intro i newIndex oldIndex
  have inside : i < degree := by
    have len := row_size table degree earlier oldBound
    change i < (tableRow table degree earlier).length at oldIndex
    omega
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ newIndex,
    Slice.Inhabited_getElem_eq_getElem! _ _ oldIndex,
    row_read _ _ _ _ newBound inside, row_read _ _ _ _ oldBound inside]
  simp only [Slice.getElem!_Nat_eq, Slice.setSlice!_val]
  rw [List.getElem!_setSlice!_prefix _ _ _ _ (by rw [Nat.add_mul, Nat.one_mul] at stop; omega)]

private theorem pure_step_image {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : ExactScaleXor kernels) (modulus current : Slice U64) (degree : Nat)
    (positive : 0 < degree) (shape : modulus.length = degree + 1)
    (monic : modulus[degree]! = 1#u64) (width : current.length = degree) :
    residue modulus (slicePolynomial (stepWords modulus current)) =
      residueX modulus * residue modulus (slicePolynomial current) := by
  obtain ⟨output, called, _, represented⟩ := shift_image kernels arithmetic current modulus
    (by omega) (by omega) (by rwa [width])
  have exactStep := stepWords_refines kernels arithmetic modulus current (by omega) (by omega)
  rw [exactStep] at called
  rw [Result.ok_injective called, represented]

private theorem initial_image {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : ExactScaleXor kernels) (modulus : Slice U64) (degree : Nat)
    (positive : 0 < degree) (shape : modulus.length = degree + 1)
    (monic : modulus[degree]! = 1#u64) :
    residue modulus (slicePolynomial (initialWords modulus degree)) = residueX modulus ^ (2 * firstHigh degree) := by
  have prefixLen : (prefixSlice modulus degree).length = degree :=
    (RebuiltLfsr.prefix_length _ _).trans (Nat.min_eq_left (by omega))
  have low := monic_low_image modulus degree shape monic
  unfold initialWords
  split
  · rw [low, show 2 * firstHigh degree = degree by unfold firstHigh; omega]
  · rw [pure_step_image kernels arithmetic modulus _ degree positive shape monic prefixLen, low, ← pow_succ',
      show 2 * firstHigh degree = degree + 1 by unfold firstHigh; omega]

private theorem fill_images {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : ExactScaleXor kernels) (modulus : Slice U64) (degree : Nat)
    (positive : 0 < degree) (shape : modulus.length = degree + 1)
    (monic : modulus[degree]! = 1#u64)
    (table current : Slice U64) (row count : Nat) (bounded : (row + count) * degree ≤ table.length)
    (width : current.length = degree)
    (earlier : ∀ i < row, residue modulus (slicePolynomial (tableRow table degree i)) =
      residueX modulus ^ (2 * (firstHigh degree + i)))
    (image : 0 < count → residue modulus (slicePolynomial current) = residueX modulus ^ (2 * (firstHigh degree + row))) :
    let output := (fillRows modulus degree table current row count).1
    output.length = table.length ∧
      ∀ i < row + count, residue modulus (slicePolynomial (tableRow output degree i)) =
        residueX modulus ^ (2 * (firstHigh degree + i)) := by
  induction count generalizing table current row with
  | zero => exact ⟨rfl, by simpa only [fillRows, Nat.add_zero] using earlier⟩
  | succ count ih =>
    let updated := table.setSlice! (row * degree) current.val
    let next := if count = 0 then current else stepWords modulus (stepWords modulus current)
    have updatedLen : updated.length = table.length := Slice.setSlice!_length _ _ _
    have written : (row + 1) * degree ≤ table.length :=
      (Nat.mul_le_mul_right _ (by omega : row + 1 ≤ row + (count + 1))).trans bounded
    have previousRoom : row * degree ≤ table.length :=
      (Nat.mul_le_mul_right _ (Nat.le_succ row)).trans written
    have frames : ∀ i < row + 1,
        residue modulus (slicePolynomial (tableRow updated degree i)) =
        residueX modulus ^ (2 * (firstHigh degree + i)) := by
      intro i active
      by_cases old : i < row
      · rw [read_before table current degree row i old previousRoom, earlier i old]
      · have same : i = row := by omega
        subst i
        rw [read_written table current degree row width written, image (by omega)]
    have nextWidth : next.length = degree := by unfold next; split <;> simp only [stepWords_length, width]
    have nextImage (positiveCount : 0 < count) :
        residue modulus (slicePolynomial next) = residueX modulus ^ (2 * (firstHigh degree + (row + 1))) := by
      unfold next
      rw [ite_eq_right (by omega), pure_step_image kernels arithmetic modulus _ degree positive shape monic
        (by rw [stepWords_length, width]), pure_step_image kernels arithmetic modulus _ degree positive shape monic width,
        image (by omega), ← pow_succ', ← pow_succ',
        show 2 * (firstHigh degree + row) + 1 + 1 = 2 * (firstHigh degree + (row + 1)) by omega]
    have updatedRoom : (row + 1 + count) * degree ≤ updated.length := by
      simpa only [updatedLen, show row + 1 + count = row + (count + 1) by omega] using bounded
    obtain ⟨len, images⟩ := ih updated next (row + 1) updatedRoom nextWidth frames nextImage
    refine ⟨len.trans updatedLen, ?_⟩
    intro i active
    exact images i (by omega)

theorem expected_table_correct {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : ExactScaleXor kernels) (modulus table work : Slice U64)
    (degreeBound : 4 ≤ modulus.length) (monic : modulus[modulus.length - 1]! = 1#u64)
    (room : (modulus.length - 1) * ((modulus.length - 1) / 2) ≤ table.length) :
    CorrectTable modulus (expectedTable modulus table work).1 (modulus.length - 1) := by
  let degree := modulus.length - 1
  have shape : modulus.length = degree + 1 := by omega
  have startWidth := initialWords_length modulus degree (by omega)
  obtain ⟨tableLen, rows⟩ := fill_images kernels arithmetic modulus degree (by omega) shape monic
    table (initialWords modulus degree) 0 (degree / 2)
    (by simpa only [Nat.zero_add, Nat.mul_comm] using room) startWidth (by simp)
    (fun _ => by simpa only [Nat.add_zero] using initial_image kernels arithmetic modulus degree (by omega) shape monic)
  change CorrectTable modulus (fillRows modulus degree table (initialWords modulus degree) 0 (degree / 2)).1 degree
  exact ⟨by rwa [tableLen], fun i bound => rows i (by omega)⟩

/-- The original generated body returns a table that represents all high
even powers, with the precise work and table writeback of expectedTable. -/
def ActualDenseTableAlgebra : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    ExactScaleXor kernels →
    ∀ (modulus table work : Slice U64),
      4 ≤ modulus.length → modulus[modulus.length - 1]! = 1#u64 →
      (modulus.length - 1) * ((modulus.length - 1) / 2) ≤ table.length →
      4 * modulus.length ≤ work.length →
      ∃ tableOut workOut,
        bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.prepare_square_table
          fieldDictionary kernels modulus table work = .ok (tableOut, workOut) ∧
        CorrectTable modulus tableOut (modulus.length - 1)

theorem prepare_square_table_algebra : ActualDenseTableAlgebra := by
  intro K kernels arithmetic modulus table work length monic room workRoom
  exact ⟨_, _, prepare_square_table_refines kernels arithmetic modulus table work length monic room workRoom,
    expected_table_correct kernels arithmetic modulus table work length monic room⟩

end BulksketchBridge.DenseReducerTable
