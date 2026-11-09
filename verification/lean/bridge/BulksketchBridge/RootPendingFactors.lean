import BulksketchBridge.RootPendingLayout
import BulksketchBridge.DenseGcd

namespace BulksketchBridge.RootRun

open Aeneas.Std ClosedLeafAdvance DenseCoefficient RebuiltLfsr SliceKernels
open Algebra.Gf64 Polynomial
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open ClosedLeaf (region)

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def pendingCoefficients (workspace : RowWorkspace) (frame : FactorFrame) : Slice U64 :=
  region workspace.factors frame.coefficient_start.val
    (frame.coefficient_start.val + frame.coefficient_len.val)

noncomputable def pendingFactor (workspace : RowWorkspace) (frame : FactorFrame) : Polynomial Field :=
  slicePolynomial (pendingCoefficients workspace frame)

noncomputable def activeFactor (roots : Roots) (workspace : RowWorkspace) : Polynomial Field :=
  slicePolynomial (prefixSlice workspace.polynomials (roots.degree.val + 1))

theorem popped_factor (roots : Roots) (workspace : RowWorkspace) (frame : FactorFrame)
    (bounds : PopBounds roots workspace frame) :
    activeFactor (poppedRoots roots workspace frame) (poppedWorkspace workspace frame) =
      pendingFactor workspace frame := by
  obtain ⟨_, _, positive, polynomialRoom, factorRoom, _⟩ := bounds
  let coefficients := pendingCoefficients workspace frame
  have coefficientLen : coefficients.length = frame.coefficient_len.val := by
    unfold coefficients pendingCoefficients
    rw [ClosedLeaf.region_length _ _ _ factorRoom]
    omega
  have copied : (poppedWorkspace workspace frame).polynomials = restorePrefix workspace.polynomials coefficients := by
    unfold poppedWorkspace
    dsimp only
    congr 1
    apply Slice.ext
    simp only [coefficients, pendingCoefficients, region, Slice.from_val, List.slice, Nat.add_sub_cancel_left]
  have size : (poppedRoots roots workspace frame).degree.val + 1 = frame.coefficient_len.val := by
    change (usizeWord (frame.coefficient_len.val - 1)).val + 1 = _
    rw [word_val _ ((Nat.sub_le ..).trans (polynomialRoom.trans workspace.polynomials.length_ineq))]
    omega
  unfold activeFactor pendingFactor
  rw [size, copied, ← coefficientLen, DenseGcd.prefix_restored]
  exact coefficientLen ▸ polynomialRoom

/-- The source pop restores exactly the polynomial owned by the top
    pending frame, and keeps all lower frames admitted. -/
def ActualAdvanceRestoresFactor : Prop :=
  ∀ (roots : Roots) (workspace : RowWorkspace),
    PendingLayout roots workspace.stack workspace.factors.length workspace.polynomials.length →
    roots.pending ≠ 0#usize →
    ∃ frame, workspace.stack.val[roots.pending.val - 1]? = some frame ∧
      let after := poppedRoots roots workspace frame
      let written := poppedWorkspace workspace frame
      Roots.advance roots workspace = .ok (stageFor after, after, written, id) ∧
      activeFactor after written = pendingFactor workspace frame ∧
      PendingLayout after written.stack written.factors.length written.polynomials.length

theorem advance_restores_factor : ActualAdvanceRestoresFactor := by
  intro roots workspace layout active
  obtain ⟨frame, bounds, _⟩ := pop_bounds_of_pending_layout roots workspace layout active
  exact ⟨frame, bounds.2.1, advance_pop_refines roots workspace frame bounds, popped_factor roots workspace frame bounds,
    popped_pending_layout roots workspace frame layout⟩

open RootDivide in
theorem exact_division_product (a b q rem : Slice U64) (raw : Slice RawProduct)
    (positive : 0 < b.length) (leading : b[b.length - 1]! ≠ 0#u64)
    (qRoom : a.length + 1 ≤ q.length) (remRoom : a.length + 1 ≤ rem.length)
    (rawRoom : a.length + 1 ≤ raw.length) (length : Usize)
    (exact : (exactDivisionResult a b q rem raw).1 = some length) :
    slicePolynomial a = slicePolynomial b *
      slicePolynomial (prefixSlice (exactDivisionResult a b q rem raw).2.1 length.val) := by
  let inverse := DenseDivision.divisorInverse b[b.length - 1]!
  let out := DenseDivision.expectedDivRem a b q rem raw inverse
  have product := (DenseDivision.model_meaning a b q rem raw inverse positive qRoom remRoom rawRoom
    (DenseDivision.divisor_inverse_law _ leading)).1
  change slicePolynomial a =
    slicePolynomial (prefixSlice out.2.1 out.1.1.val) * slicePolynomial b +
      slicePolynomial (prefixSlice out.2.2.1 out.1.2.val) at product
  by_cases zero : out.1.2 = 0#usize
  · have exactResult : exactDivisionResult a b q rem raw =
        (some out.1.1, out.2.1, out.2.2.1, out.2.2.2) := by
      unfold exactDivisionResult
      exact ite_eq_left zero
    rw [exactResult] at exact ⊢
    have lengthEq : out.1.1 = length := Option.some.inj exact
    rw [zero, lengthEq] at product
    simp only [show (0#usize).val = 0 by decide] at product
    have empty : slicePolynomial (prefixSlice out.2.2.1 0) = 0 := by
      simp only [slicePolynomial, prefix_length, Nat.zero_min, Finset.range_zero, Finset.sum_empty]
    rw [empty, add_zero, mul_comm] at product
    exact product
  · have exactResult : (exactDivisionResult a b q rem raw).1 = none := by
      unfold exactDivisionResult
      rw [ite_eq_right zero]
    rw [exactResult] at exact
    contradiction

open RootDivide in
/-- The exact factor commit stores the quotient in the new slot and
    replaces the active modulus prefix by the GCD. The affine base
    word lies outside the copied quotient. -/
theorem committed_coefficients (roots : Roots) (buffers : FactorWork) (factors : Slice U64)
    (stack : Slice FactorFrame) (meter : WorkMeter) (length start : Usize)
    (quotient remainder : Slice U64) (raw : Slice RawProduct)
    (positive : 0 < length.val) (quotientRoom : length.val ≤ quotient.length)
    (lengthRoom : length.val ≤ roots.stride.val)
    (slotEnd : start.val + roots.stride.val ≤ factors.length)
    (affineRoom : roots.affine = true → length.val < roots.stride.val)
    (gcdRoom : roots.gcd_len.val ≤ buffers.gcd.length)
    (modulusRoom : roots.gcd_len.val ≤ buffers.modulus.length) :
    let output := committed roots buffers factors stack meter length start quotient remainder raw
    prefixSlice output.2.2.1.modulus roots.gcd_len.val = prefixSlice buffers.gcd roots.gcd_len.val ∧
      region output.2.2.2.2.1 start.val (start.val + length.val) = prefixSlice quotient length.val := by
  let output := committed roots buffers factors stack meter length start quotient remainder raw
  let right := prefixSlice quotient length.val
  let left := prefixSlice buffers.gcd roots.gcd_len.val
  let copied := factors.setSlice! start.val right.val
  let written := output.2.2.2.2.1
  have rightLen : right.length = length.val := by
    rw [show right = prefixSlice quotient length.val from rfl, prefix_length, Nat.min_eq_left quotientRoom]
  have leftLen : left.length = roots.gcd_len.val := by
    rw [show left = prefixSlice buffers.gcd roots.gcd_len.val from rfl, prefix_length, Nat.min_eq_left gcdRoom]
  have leftCopy : output.2.2.1.modulus = restorePrefix buffers.modulus left := rfl
  have leftMeaning : prefixSlice output.2.2.1.modulus roots.gcd_len.val = left := by
    rw [leftCopy, ← leftLen, DenseGcd.prefix_restored]
    rwa [leftLen]
  have writtenLen : written.length = factors.length := by
    cases affine : roots.affine <;>
      simp only [written, output, committed, affine, Bool.false_eq_true, ite_false, ite_true,
        Slice.set_length, Slice.setSlice!_length]
  have rightEnd : start.val + length.val ≤ written.length := by
    rw [writtenLen]
    omega
  have exactWord (index : Nat) (active : index < length.val) :
      written[start.val + index]! = right[index]! := by
    have copiedWord : copied[start.val + index]! = right[index]! := by
      unfold copied
      rw [Slice.setSlice!_getElem!_middle _ _ _ _ (by
        have width : right.val.length = length.val := rightLen
        omega), show start.val + index - start.val = index by omega, ← Slice.getElem!_Nat_eq]
    cases affine : roots.affine with
    | false => simpa only [written, output, committed, affine, Bool.false_eq_true, ite_false, copied] using copiedWord
    | true =>
      let base := usizeWord (start.val + roots.stride.val - 1)
      let rank := usizeWord (roots.affine_rank.val - 1)
      let word := (buffers.basis.directions.map fun basis => basis[rank.val]!).getD 0#u64
      have baseValue : base.val = start.val + roots.stride.val - 1 :=
        word_val _ ((Nat.sub_le ..).trans (slotEnd.trans factors.length_ineq))
      have belowBase : start.val + index < base.val := by rw [baseValue]; have := affineRoom affine; omega
      simp only [written, output, committed, affine, ite_true]
      change (copied.set base (roots.affine_base ^^^ word))[start.val + index]! = _
      rw [Slice.getElem!_Nat_set_ne _ _ _ _ (by omega)]
      exact copiedWord
  refine ⟨leftMeaning, ?_⟩
  change region written start.val (start.val + length.val) = right
  have regionLen : (region written start.val (start.val + length.val)).length = length.val := by
    rw [ClosedLeaf.region_length _ _ _ rightEnd]
    omega
  apply Slice.ext_getElem (regionLen.trans rightLen.symm)
  intro index inRegion inRight
  have active : index < length.val := by change index < right.length at inRight; omega
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ inRegion, Slice.Inhabited_getElem_eq_getElem! _ _ inRight]
  have regionWord : (region written start.val (start.val + length.val))[index]! = written[start.val + index]! := by
    simp only [region, Slice.getElem!_Nat_eq, Slice.from_val]
    exact List.getElem!_slice _ _ _ _ ⟨rightEnd, by omega⟩
  rw [regionWord, exactWord index active]

end BulksketchBridge.RootRun
