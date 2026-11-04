import BulksketchBridge.MapsQuadraticValue
import BulksketchBridge.MapsTraceMath
import BulksketchBridge.Square
import BulksketchProofs.Field.Maps

/-!
Composition of unchanged native table lookup/solver bodies with independent
full-word matrix identities. Every input is admitted; the real source assert is
proved true on its selected path. No successful-result premise is assumed.
-/

namespace BulksketchBridge.MapsQuadratic

open Aeneas Aeneas.Std BulksketchProofs.Field

/-- The complete native16-nibble output equals the independent64-column matrix map. -/
theorem quadratic_value_matches_matrix : MapsQuadraticChallenges.actualValueMatchesIndependentMatrix := by
  intro input
  rw [quadratic_value_refines input]
  apply congrArg Result.ok
  apply U64.bv_eq_imp_eq
  exact Maps.chunk_lookup_eq_matrix input.bv

private theorem matrix_root_bits (input : U64) (clear : Maps.traceBit input.bv = false) :
    Maps.quadratic (Maps.quadraticValue input.bv) = input.bv := by
  apply (Maps.quadratic_right_inverse input.bv).trans
  unfold Maps.traceProjection
  rw [clear]
  simp only [Bool.false_eq_true, ite_false]
  exact BitVec.xor_zero

private theorem matrix_is_root_when_trace_zero (input : U64)
    (clear : Maps.traceBit input.bv = false) :
    Square.expectedWord (expectedMatrixWord input) ^^^ expectedMatrixWord input = input := by
  apply U64.bv_eq_imp_eq
  exact matrix_root_bits input clear

/-- The original solver returns None on trace one and its exact normalized matrix
solution otherwise. The actual square/assert and both return paths are included. -/
theorem solve_quadratic_refines : MapsQuadraticChallenges.actualSolverMatchesNormalizedModel := by
  intro input
  unfold bulksketch.field.maps.solve_quadratic
  rw [MapsTrace.trace_refines input]
  simp only [bind_ok]
  rw [MapsTraceMath.trace_byte_case input]
  cases traceCase : Maps.traceBit input.bv with
  | false =>
    have assertion := matrix_is_root_when_trace_zero input traceCase
    simp [traceCase, quadratic_value_matches_matrix input,
      Square.square_refines, assertion, expectedSolution, lift, bind_ok]
  | true =>
    simp [traceCase, expectedSolution]

/-- Returned roots are exact, bit-zero normalized and unique; rejection means
trace one. Every original native call is proved to return normally. -/
theorem solve_quadratic_exact_meaning : MapsQuadraticChallenges.actualSolverHasExactNormalizedSolutionMeaning := by
  intro input
  refine ⟨expectedSolution input, solve_quadratic_refines input, ?_⟩
  cases traceCase : Maps.traceBit input.bv with
  | false =>
    simp only [expectedSolution, traceCase, Bool.false_eq_true, ite_false]
    refine ⟨matrix_root_bits input traceCase, Maps.quadraticValue_bit_zero input.bv, ?_⟩
    intro other equation normalized
    exact Maps.normalized_solution_unique input.bv other equation normalized
  | true =>
    simp only [expectedSolution, traceCase, ite_true]

end BulksketchBridge.MapsQuadratic
