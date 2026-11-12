import BulksketchBridge.DenseSquarePolynomialSpec
import BulksketchBridge.DenseSquare
import Mathlib.Algebra.CharP.Algebra

namespace BulksketchBridge.DenseSquare

open Aeneas.Std Polynomial BulksketchBridge.Algebra.Gf64
open DenseSquareChallenges SliceKernels DenseCoefficient

private theorem exact_square (a dst output : Slice U64)
    (size : 2 * a.length ≤ dst.length) (length : output.length = dst.length)
    (frame : ∀ i, i < dst.length → output[i]! = coefficient a dst i) :
    slicePolynomial (prefixSlice output (2 * a.length)) = slicePolynomial a ^ 2 := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  rw [← Polynomial.map_frobenius_expand (p := 2)]
  ext index
  rw [prefix_coeff output _ index (by omega), Polynomial.coeff_map,
    Polynomial.coeff_expand (by decide : 0 < 2), slicePolynomial_coeff]
  by_cases even : index % 2 = 0
  · have divides : 2 ∣ index := Nat.dvd_of_mod_eq_zero even
    by_cases active : index < 2 * a.length
    · have inSource : index / 2 < a.length := by omega
      rw [ite_eq_left active, ite_eq_left divides, ite_eq_left inSource,
        frame index (by omega)]
      simp only [coefficient, active, even, ite_true]
      exact toField_square a[index / 2]!.bv
    · have inSource : ¬ index / 2 < a.length := by omega
      simp only [active, divides, inSource, ite_false, ite_true, map_zero]
  · have odd : ¬ 2 ∣ index := by simpa only [Nat.dvd_iff_mod_eq_zero] using even
    by_cases active : index < 2 * a.length
    · rw [ite_eq_left active, ite_eq_right odd, frame index (by omega)]
      simp only [coefficient, active, even, ite_true, ite_false, map_zero]
      exact toField_zero
    · simp only [active, odd, ite_false, map_zero]

theorem square_into_polynomial_refines : SquareIntoPolynomialRefines := by
  intro Backend kernels nativeSquare a dst raw machine destination scratch
  have result := square_into_refines Backend kernels nativeSquare a dst raw
  rw [ite_eq_left machine, ite_eq_left ⟨destination, scratch⟩] at result
  obtain ⟨length, output, normal, outputLength, frame, canonical⟩ := result
  refine ⟨length, output, normal, ?_⟩
  rw [canonical, normalized_prefix_polynomial output (2 * a.length) (by omega)]
  exact exact_square a dst output destination outputLength frame

end BulksketchBridge.DenseSquare
