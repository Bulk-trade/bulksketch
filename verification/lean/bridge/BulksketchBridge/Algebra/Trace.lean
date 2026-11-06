import BulksketchBridge.Algebra.TraceChallenges
import BulksketchBridge.Algebra.WordSquare
import BulksketchProofs.Field.Maps

/-!
# Transport to Mathlib's `Algebra.trace`

The coefficient map is proved to preserve XOR and polynomial squaring.  Thus
the word trace's original 64 conjugates map to the finite-field conjugates in
Mathlib's algebra trace formula.  No definition of a substitute trace is used.
-/

namespace BulksketchBridge.Algebra.Gf64

open BulksketchProofs.Field
open scoped BigOperators

/-- Every source-model repeated square is the corresponding quotient-field power. -/
theorem toField_iterateSquare (count : Nat) (input : BitVec 64) :
    toField (Period.iterateSquare count input) = toField input ^ (2 ^ count) := by
  induction count with
  | zero => simp [Period.iterateSquare]
  | succ count inductionHypothesis =>
    rw [Period.iterateSquare, toField_square, inductionHypothesis, ← pow_mul, pow_succ]

/-- The independently specified word conjugate sum maps to the algebraic sum. -/
theorem toField_conjugate_sum (count : Nat) (input : BitVec 64) :
    toField (Maps.traceSumPrefix count input) =
      ∑ index ∈ Finset.range count, toField input ^ (2 ^ index) := by
  induction count with
  | zero =>
    change toField (0 : BitVec 64) = 0
    exact toField_zero
  | succ count inductionHypothesis =>
    rw [Maps.traceSumPrefix, toField_xor, inductionHypothesis,
      toField_iterateSquare, Finset.sum_range_succ]

/-- The original word-model trace is Mathlib's quotient-field trace, including
its complete zero/one value after embedding from the base field. -/
theorem word_absolute_trace_transport : TraceChallenges.wordAbsoluteTraceIsAlgebraTrace := by
  intro input
  rw [Maps.absoluteTrace_is_sum, toField_conjugate_sum,
    algebra_trace_conjugate_sum]

/-- The implementation's two selected coefficient bits compute the actual
Mathlib algebra trace in the two-element scalar field. -/
theorem native_selector_trace_transport : TraceChallenges.nativeSelectorIsAlgebraTrace := by
  intro input
  apply FaithfulSMul.algebraMap_injective (ZMod 2) Field
  rw [← word_absolute_trace_transport input, Maps.absoluteTrace_eq_selector]
  cases bitCase : Maps.traceBit input
  · simp only [Maps.traceWord, bitCase, Bool.false_eq_true, ite_false, map_zero]
    exact toField_zero
  · simp only [Maps.traceWord, bitCase, ite_true, map_one]
    exact toField_one

end BulksketchBridge.Algebra.Gf64
