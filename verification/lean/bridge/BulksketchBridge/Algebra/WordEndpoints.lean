import BulksketchBridge.Algebra.WordEquiv
import BulksketchBridge.Algebra.WordSquare
import BulksketchBridge.Algebra.WordLaws
import BulksketchBridge.Algebra.WordChallenges

namespace BulksketchBridge.Algebra.Gf64

theorem exact_polynomial_coefficients : WordChallenges.ExactPolynomialCoefficients := by
  intro width input index
  exact wordPolynomial_coeff input index

theorem bijective_representation : WordChallenges.BijectiveRepresentation :=
  ⟨toField_injective, toField_surjective⟩

theorem additive_representation : WordChallenges.AdditiveRepresentation :=
  ⟨toField_zero, toField_one, toField_xor⟩

theorem complete_raw_product : WordChallenges.CompleteRawProduct := wordPolynomial_clmul

theorem reduction_representation : WordChallenges.ReductionRepresentation := toField_reduce

theorem multiplication_representation : WordChallenges.MultiplicationRepresentation := toField_mul

theorem square_representation : WordChallenges.SquareRepresentation := toField_square

end BulksketchBridge.Algebra.Gf64
