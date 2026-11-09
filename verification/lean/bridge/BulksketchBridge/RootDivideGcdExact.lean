import BulksketchBridge.RootDivideDegree

namespace BulksketchBridge.RootDivide

open Aeneas.Std Algebra.Gf64 DenseCoefficient RebuiltLfsr BmEntry SliceKernels Polynomial
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial (exact_divide_into)

set_option maxRecDepth 4096
set_option maxHeartbeats 1300000

private theorem native_inputs (roots : Roots) (buffers : FactorWork)
    (ready : NativeDivideReady roots buffers) :
    let divisor := prefixSlice buffers.gcd roots.gcd_len.val
    let quotient := prefixSlice buffers.work (roots.degree.val + 2)
    let remainder := tail buffers.work (roots.degree.val + 2)
    0 < divisor.length ∧ divisor[divisor.length - 1]! ≠ 0#u64 ∧
    buffers.modulus.length + 1 ≤ quotient.length ∧
    buffers.modulus.length + 1 ≤ remainder.length ∧
    buffers.modulus.length + 1 ≤ buffers.raw.length := by
  have divisorLength : (prefixSlice buffers.gcd roots.gcd_len.val).length = roots.gcd_len.val :=
    (prefix_length _ _).trans (Nat.min_eq_left ready.gcdRoom)
  have quotientLength : (prefixSlice buffers.work (roots.degree.val + 2)).length =
      roots.degree.val + 2 := (prefix_length _ _).trans (Nat.min_eq_left ready.workRoom)
  have remainderLength := tail_length buffers.work (roots.degree.val + 2)
  simp only [divisorLength, quotientLength, remainderLength]
  exact ⟨ready.divisorPositive, ready.divisorNonzero, ready.quotientRoom, ready.remainderRoom, ready.rawRoom⟩

/-- Divisibility gives the Some branch of the original exact-division
    model, including its native normalized quotient length. -/
theorem native_call_some_of_factor (roots : Roots) (buffers : FactorWork)
    (ready : NativeDivideReady roots buffers)
    (factor : slicePolynomial (prefixSlice buffers.gcd roots.gcd_len.val) ∣
      slicePolynomial buffers.modulus) :
    ∃ length : Usize, (nativeCall roots buffers).1 = some length := by
  let divisor := prefixSlice buffers.gcd roots.gcd_len.val
  let quotient := prefixSlice buffers.work (roots.degree.val + 2)
  let remainder := tail buffers.work (roots.degree.val + 2)
  obtain ⟨positive, leading, qRoom, remRoom, rawRoom⟩ := native_inputs roots buffers ready
  let inverse := DenseDivision.divisorInverse divisor[divisor.length - 1]!
  let out := DenseDivision.expectedDivRem buffers.modulus divisor quotient remainder buffers.raw inverse
  have remainderZero : out.1.2.val = 0 :=
    (DenseDivision.model_exact_iff_dvd buffers.modulus divisor quotient remainder buffers.raw
      positive leading qRoom remRoom rawRoom).mpr factor
  have empty : out.1.2 = 0#usize := UScalar.eq_of_val_eq remainderZero
  have frame : nativeCall roots buffers =
      if out.1.2 = 0#usize then (some out.1.1, out.2.1, out.2.2.1, out.2.2.2)
      else (none, DenseDivision.cleared out.2.1 (buffers.modulus.length + 1), out.2.2.1, out.2.2.2) := rfl
  refine ⟨out.1.1, ?_⟩
  rw [frame, ite_eq_left empty]

/-- A native proper GCD split has an exact nonconstant quotient. The GCD
    identity is supplied by the upstream original monic-GCD stage. -/
def ActualNativeProperGcdQuotient : Prop :=
  ∀ (roots : Roots) (buffers : FactorWork) (trace : Polynomial Field),
    NativeDivideReady roots buffers → ProperDivideShape roots buffers →
    slicePolynomial (prefixSlice buffers.gcd roots.gcd_len.val) =
      gcd (slicePolynomial buffers.modulus) trace →
    ∃ length : Usize, (nativeCall roots buffers).1 = some length ∧
      let quotient := (nativeCall roots buffers).2.1
      0 < length.val - 1 ∧ length.val ≤ quotient.length ∧
      (prefixSlice quotient length.val)[length.val - 1]! ≠ 0#u64 ∧
      roots.gcd_degree.val + (length.val - 1) = roots.degree.val ∧
      slicePolynomial buffers.modulus =
        slicePolynomial (prefixSlice quotient length.val) * slicePolynomial (prefixSlice buffers.gcd roots.gcd_len.val)

theorem native_proper_gcd_has_quotient : ActualNativeProperGcdQuotient := by
  intro roots buffers trace ready shape exactGcd
  have factor : slicePolynomial (prefixSlice buffers.gcd roots.gcd_len.val) ∣
      slicePolynomial buffers.modulus := by
    rw [exactGcd]
    exact gcd_dvd_left _ _
  obtain ⟨length, success⟩ := native_call_some_of_factor roots buffers ready factor
  exact ⟨length, success, native_call_degree roots buffers ready shape length success⟩

/-- The exact native callee observed by the original divide wrapper returns
    Some for the same proper GCD and exact scratch frame. -/
theorem original_native_proper_gcd_call (division : DenseDivisionRuntime.DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (buffers : FactorWork) (trace : Polynomial Field)
    (law : DenseDivision.RefinesModel division kernels)
    (ready : NativeDivideReady roots buffers) (shape : ProperDivideShape roots buffers)
    (exactGcd : slicePolynomial (prefixSlice buffers.gcd roots.gcd_len.val) =
      gcd (slicePolynomial buffers.modulus) trace) :
    ∃ length : Usize,
      reached (exact_divide_into division) DenseGcd.dictionary kernels roots buffers (some length)
        (nativeCall roots buffers).2.1 (nativeCall roots buffers).2.2.1 (nativeCall roots buffers).2.2.2 ∧
      0 < length.val - 1 ∧ roots.gcd_degree.val + (length.val - 1) = roots.degree.val := by
  obtain ⟨length, success, positiveDegree, _, _, mass, _⟩ :=
    native_proper_gcd_has_quotient roots buffers trace ready shape exactGcd
  obtain ⟨positive, leading, qRoom, remRoom, rawRoom⟩ := native_inputs roots buffers ready
  let divisor := prefixSlice buffers.gcd roots.gcd_len.val
  let quotient := prefixSlice buffers.work (roots.degree.val + 2)
  let remainder := tail buffers.work (roots.degree.val + 2)
  let inverse := DenseDivision.divisorInverse divisor[divisor.length - 1]!
  let out := DenseDivision.expectedDivRem buffers.modulus divisor quotient remainder buffers.raw inverse
  have modeled := DenseDivision.modeled_exact_divide division kernels law buffers.modulus divisor quotient
    remainder buffers.raw positive leading qRoom remRoom rawRoom
  have frame : nativeCall roots buffers =
      if out.1.2 = 0#usize then (some out.1.1, out.2.1, out.2.2.1, out.2.2.2)
      else (none, DenseDivision.cleared out.2.1 (buffers.modulus.length + 1), out.2.2.1, out.2.2.2) := rfl
  refine ⟨length, ?_, positiveDegree, mass⟩
  unfold reached
  change exact_divide_into division DenseGcd.dictionary kernels buffers.modulus divisor quotient remainder buffers.raw =
    .ok (some length, (nativeCall roots buffers).2.1, (nativeCall roots buffers).2.2.1,
      (nativeCall roots buffers).2.2.2)
  change exact_divide_into division DenseGcd.dictionary kernels buffers.modulus divisor quotient remainder buffers.raw =
    (if out.1.2 = 0#usize then .ok (some out.1.1, out.2.1, out.2.2.1, out.2.2.2)
    else .ok (none, DenseDivision.cleared out.2.1 (buffers.modulus.length + 1), out.2.2.1, out.2.2.2)) at modeled
  rw [modeled]
  by_cases empty : out.1.2 = 0#usize
  · have size : out.1.1 = length := by
      rw [frame, ite_eq_left empty] at success
      exact Option.some.inj success
    simp only [frame, empty, ite_true, size]
  · rw [frame, ite_eq_right empty] at success
    cases success

/-- The InvalidLocator path of the original divide wrapper is excluded
    whenever its exact callee is the admitted proper GCD division. -/
theorem original_native_proper_gcd_not_none (division : DenseDivisionRuntime.DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (buffers : FactorWork) (trace : Polynomial Field)
    (law : DenseDivision.RefinesModel division kernels)
    (ready : NativeDivideReady roots buffers) (shape : ProperDivideShape roots buffers)
    (exactGcd : slicePolynomial (prefixSlice buffers.gcd roots.gcd_len.val) =
      gcd (slicePolynomial buffers.modulus) trace)
    (quotient remainder : Slice U64) (raw : Slice RawProduct) :
    ¬ reached (exact_divide_into division) DenseGcd.dictionary kernels roots buffers none quotient remainder raw := by
  intro rejected
  obtain ⟨length, accepted, _, _⟩ :=
    original_native_proper_gcd_call division kernels roots buffers trace law ready shape exactGcd
  unfold reached at rejected accepted
  have impossible : (some length : Option Usize) = none :=
    congrArg Prod.fst (Result.ok_injective (accepted.symm.trans rejected))
  cases impossible

#print axioms native_call_some_of_factor
#print axioms native_proper_gcd_has_quotient
#print axioms original_native_proper_gcd_call
#print axioms original_native_proper_gcd_not_none

end BulksketchBridge.RootDivide
