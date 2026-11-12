import BulksketchBridge.PortableChallenges
import BulksketchBridge.Algebra.WordNative
import BulksketchBridge.Algebra.TraceNative
import BulksketchBridge.MapsQuadratic

/-! Functional refinements of the seven unchanged Portable forwarding bodies.
Each proof composes with the actual source-generated Gf64 implementation. The
original extractor/runtime/compiler/machine trust boundary is unchanged. -/
namespace BulksketchBridge.Portable

open Aeneas.Std BulksketchBridge.Algebra.Gf64

theorem mul_refines : PortableChallenges.actualMultiplicationIsFieldMultiplication := by
  intro left right
  exact ⟨native_mul_word left right, toField_mul left.bv right.bv⟩

theorem square_refines : PortableChallenges.actualSquareIsFieldSquare := by
  intro input
  exact ⟨Square.square_refines input, toField_square input.bv⟩

theorem frobenius_refines : PortableChallenges.actualFrobeniusIsFullFieldPower := by
  intro input power
  exact ⟨FrobeniusPeriod.native_unmodded_refines input power,
    toField_iterateSquare power.val input.bv⟩

theorem trace_refines : PortableChallenges.actualTraceIsAlgebraTrace := by
  intro input
  exact native_trace_is_algebra_trace input

/-- Source normality, exact scalar trace rejection and normalized uniqueness
are preserved when the quadratic equation is interpreted in Mathlib's field. -/
theorem solve_quadratic_refines : PortableChallenges.actualQuadraticHasNormalizedFieldMeaning := by
  intro input
  obtain ⟨output, normal, meaning⟩ := MapsQuadratic.solve_quadratic_exact_meaning input
  refine ⟨output, normal, ?_⟩
  cases output with
  | none =>
    rw [native_selector_trace_transport, meaning]
    rfl
  | some solution =>
    obtain ⟨equation, normalized, unique⟩ := meaning
    refine ⟨?_, normalized, ?_⟩
    · have interpreted := congrArg toField equation
      simpa only [BulksketchProofs.Field.Maps.quadratic, toField_xor,
        toField_square] using interpreted
    · intro other equation normalized
      apply unique other ?_ normalized
      apply toField_injective
      simpa only [BulksketchProofs.Field.Maps.quadratic, toField_xor,
        toField_square] using equation

theorem raw_mul_refines : PortableChallenges.actualRawMultiplicationReturnsFullProduct := by
  intro left right
  exact RawMul.raw_mul_refines left right

theorem reduce_refines : PortableChallenges.actualReductionIsExactQuotientRemainder := by
  intro product
  obtain ⟨output, normal, exactBits, _⟩ := Gf64Reduce.reduce_refines product
  refine ⟨output, normal, exactBits, ?_⟩
  rw [exactBits]
  exact toField_reduce product.lo.bv product.hi.bv

end BulksketchBridge.Portable
