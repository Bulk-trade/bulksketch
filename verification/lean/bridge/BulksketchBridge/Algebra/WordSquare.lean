import BulksketchBridge.Algebra.WordOps
import BulksketchProofs.Field.Spread
import Mathlib.Algebra.Polynomial.Expand

/-! The complete 128-bit square has exactly the coefficients of the polynomial
square.  The independently proved division certificate then transports the
native reduction to the actual Mathlib quotient. -/

namespace BulksketchBridge.Algebra.Gf64

open Polynomial BulksketchProofs.Field

/-- All 128 raw-square coefficients, before the quotient reduction. -/
theorem wordPolynomial_rawSquare (input : BitVec 64) :
    wordPolynomial (rawSquare128 input) = wordPolynomial input ^ 2 := by
  have expanded : wordPolynomial (rawSquare128 input) =
      Polynomial.expand (ZMod 2) 2 (wordPolynomial input) := by
    ext index
    rw [wordPolynomial_coeff, coeff_expand (by decide : 0 < 2), wordPolynomial_coeff]
    by_cases bound : index < 128
    · rw [rawSquare128_bits input index bound]
      by_cases even : index % 2 = 0
      · have divides : 2 ∣ index := Nat.dvd_of_mod_eq_zero even
        simp [even, divides]
      · have notDivides : ¬2 ∣ index := by simpa only [Nat.dvd_iff_mod_eq_zero] using even
        simp [even, notDivides]
    · rw [BitVec.getLsbD_of_ge (rawSquare128 input) index (by omega)]
      rw [BitVec.getLsbD_of_ge input (index / 2) (by omega)]
      simp
  rw [expanded]
  have characteristicSquare :=
    Polynomial.map_frobenius_expand (p := 2) (wordPolynomial input)
  simpa only [ZMod.frobenius_zmod, Polynomial.map_id] using characteristicSquare

/-- The full native-shaped square word maps to the square in Mathlib's field. -/
theorem toField_square (input : BitVec 64) :
    toField (Period.squareWord input) = toField input ^ 2 := by
  rw [Period.squareWord, toField_reduce]
  change AdjoinRoot.mk modulus (wordPolynomial (rawSquare128 input)) = _
  rw [wordPolynomial_rawSquare, map_pow]
  rfl

end BulksketchBridge.Algebra.Gf64
