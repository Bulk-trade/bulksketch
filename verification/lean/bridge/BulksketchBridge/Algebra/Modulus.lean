import BulksketchBridge.Algebra.ModulusCertificates
import BulksketchBridge.Algebra.ModulusChallenges
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

/-!
# Irreducibility of the exact GF64 modulus

The proof uses the finite-field factor-degree theorem from pinned Mathlib and
explicit kernel-checked polynomial certificates. No result about native GF64
arithmetic, a pre-existing field quotient, or native evaluation is assumed.
-/

namespace BulksketchBridge.Algebra.Gf64

open Polynomial

set_option maxRecDepth 4096

/-- A checked opaque package preserves the exact power equation without expansion. -/
private noncomputable opaque frobeniusPackage :
    {function : Nat → Polynomial (ZMod 2) // ∀ count, function count = X ^ (2 ^ count)} :=
  ⟨fun count => X ^ (2 ^ count), fun _ => rfl⟩

/-- The exact Frobenius polynomial, kept symbolic for kernel-checking performance. -/
noncomputable def frobeniusPolynomial (count : Nat) : Polynomial (ZMod 2) :=
  frobeniusPackage.val count

private theorem frobeniusPolynomial_eq (count : Nat) :
    frobeniusPolynomial count = X ^ (2 ^ count) :=
  frobeniusPackage.property count

private theorem factor_degree_criterion {factor : Polynomial (ZMod 2)}
    (irreducible : Irreducible factor) (count : Nat) :
    factor.natDegree ∣ count ↔ factor ∣ frobeniusPolynomial count - X := by
  have criterion := irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := count)
  rw [Nat.card_zmod] at criterion
  rw [frobeniusPolynomial_eq]
  exact criterion

private theorem divisor_of_square_certificate {left right quotient : Polynomial (ZMod 2)}
    (certificate : left ^ 2 + modulus * quotient + right = 0) :
    modulus ∣ left ^ 2 - right := by
  refine ⟨quotient, ?_⟩
  rw [CharTwo.sub_eq_add]
  apply CharTwo.add_eq_zero.mp
  simpa only [add_right_comm] using certificate

private theorem next_frobenius {left right : Polynomial (ZMod 2)} {count : Nat}
    (previous : modulus ∣ frobeniusPolynomial count - left)
    (step : modulus ∣ left ^ 2 - right) :
    modulus ∣ frobeniusPolynomial (count + 1) - right := by
  simp only [frobeniusPolynomial_eq] at previous ⊢
  rw [pow_succ, pow_mul]
  have squared := dvd_trans previous (sub_dvd_pow_sub_pow (X ^ (2 ^ count)) left 2)
  simpa only [sub_add_sub_cancel] using dvd_add squared step

private noncomputable def remainderAt : Nat → Polynomial (ZMod 2)
  | 0 => remainder0
  | 1 => remainder1
  | 2 => remainder2
  | 3 => remainder3
  | 4 => remainder4
  | 5 => remainder5
  | 6 => remainder6
  | 7 => remainder7
  | 8 => remainder8
  | 9 => remainder9
  | 10 => remainder10
  | 11 => remainder11
  | 12 => remainder12
  | 13 => remainder13
  | 14 => remainder14
  | 15 => remainder15
  | 16 => remainder16
  | 17 => remainder17
  | 18 => remainder18
  | 19 => remainder19
  | 20 => remainder20
  | 21 => remainder21
  | 22 => remainder22
  | 23 => remainder23
  | 24 => remainder24
  | 25 => remainder25
  | 26 => remainder26
  | 27 => remainder27
  | 28 => remainder28
  | 29 => remainder29
  | 30 => remainder30
  | 31 => remainder31
  | 32 => remainder32
  | 33 => remainder33
  | 34 => remainder34
  | 35 => remainder35
  | 36 => remainder36
  | 37 => remainder37
  | 38 => remainder38
  | 39 => remainder39
  | 40 => remainder40
  | 41 => remainder41
  | 42 => remainder42
  | 43 => remainder43
  | 44 => remainder44
  | 45 => remainder45
  | 46 => remainder46
  | 47 => remainder47
  | 48 => remainder48
  | 49 => remainder49
  | 50 => remainder50
  | 51 => remainder51
  | 52 => remainder52
  | 53 => remainder53
  | 54 => remainder54
  | 55 => remainder55
  | 56 => remainder56
  | 57 => remainder57
  | 58 => remainder58
  | 59 => remainder59
  | 60 => remainder60
  | 61 => remainder61
  | 62 => remainder62
  | 63 => remainder63
  | 64 => remainder64
  | _ => 0

private theorem each_square_step (count : Nat) (bound : count < 64) :
    modulus ∣ remainderAt count ^ 2 - remainderAt (count + 1) := by
  interval_cases count
  · exact divisor_of_square_certificate square_certificate_0
  · exact divisor_of_square_certificate square_certificate_1
  · exact divisor_of_square_certificate square_certificate_2
  · exact divisor_of_square_certificate square_certificate_3
  · exact divisor_of_square_certificate square_certificate_4
  · exact divisor_of_square_certificate square_certificate_5
  · exact divisor_of_square_certificate square_certificate_6
  · exact divisor_of_square_certificate square_certificate_7
  · exact divisor_of_square_certificate square_certificate_8
  · exact divisor_of_square_certificate square_certificate_9
  · exact divisor_of_square_certificate square_certificate_10
  · exact divisor_of_square_certificate square_certificate_11
  · exact divisor_of_square_certificate square_certificate_12
  · exact divisor_of_square_certificate square_certificate_13
  · exact divisor_of_square_certificate square_certificate_14
  · exact divisor_of_square_certificate square_certificate_15
  · exact divisor_of_square_certificate square_certificate_16
  · exact divisor_of_square_certificate square_certificate_17
  · exact divisor_of_square_certificate square_certificate_18
  · exact divisor_of_square_certificate square_certificate_19
  · exact divisor_of_square_certificate square_certificate_20
  · exact divisor_of_square_certificate square_certificate_21
  · exact divisor_of_square_certificate square_certificate_22
  · exact divisor_of_square_certificate square_certificate_23
  · exact divisor_of_square_certificate square_certificate_24
  · exact divisor_of_square_certificate square_certificate_25
  · exact divisor_of_square_certificate square_certificate_26
  · exact divisor_of_square_certificate square_certificate_27
  · exact divisor_of_square_certificate square_certificate_28
  · exact divisor_of_square_certificate square_certificate_29
  · exact divisor_of_square_certificate square_certificate_30
  · exact divisor_of_square_certificate square_certificate_31
  · exact divisor_of_square_certificate square_certificate_32
  · exact divisor_of_square_certificate square_certificate_33
  · exact divisor_of_square_certificate square_certificate_34
  · exact divisor_of_square_certificate square_certificate_35
  · exact divisor_of_square_certificate square_certificate_36
  · exact divisor_of_square_certificate square_certificate_37
  · exact divisor_of_square_certificate square_certificate_38
  · exact divisor_of_square_certificate square_certificate_39
  · exact divisor_of_square_certificate square_certificate_40
  · exact divisor_of_square_certificate square_certificate_41
  · exact divisor_of_square_certificate square_certificate_42
  · exact divisor_of_square_certificate square_certificate_43
  · exact divisor_of_square_certificate square_certificate_44
  · exact divisor_of_square_certificate square_certificate_45
  · exact divisor_of_square_certificate square_certificate_46
  · exact divisor_of_square_certificate square_certificate_47
  · exact divisor_of_square_certificate square_certificate_48
  · exact divisor_of_square_certificate square_certificate_49
  · exact divisor_of_square_certificate square_certificate_50
  · exact divisor_of_square_certificate square_certificate_51
  · exact divisor_of_square_certificate square_certificate_52
  · exact divisor_of_square_certificate square_certificate_53
  · exact divisor_of_square_certificate square_certificate_54
  · exact divisor_of_square_certificate square_certificate_55
  · exact divisor_of_square_certificate square_certificate_56
  · exact divisor_of_square_certificate square_certificate_57
  · exact divisor_of_square_certificate square_certificate_58
  · exact divisor_of_square_certificate square_certificate_59
  · exact divisor_of_square_certificate square_certificate_60
  · exact divisor_of_square_certificate square_certificate_61
  · exact divisor_of_square_certificate square_certificate_62
  · exact divisor_of_square_certificate square_certificate_63

private theorem every_frobenius_certificate (count : Nat) (bound : count ≤ 64) :
    modulus ∣ frobeniusPolynomial count - remainderAt count := by
  induction count with
  | zero =>
    simp only [frobeniusPolynomial_eq, remainderAt, remainder0, pow_zero, pow_one, sub_self,
      dvd_zero]
  | succ count inductionHypothesis =>
    have countLt : count < 64 := Nat.lt_of_succ_le bound
    exact next_frobenius (inductionHypothesis (Nat.le_of_lt countLt))
      (each_square_step count countLt)

/-- The two modular-power certificates used in the degree-64 Rabin criterion. -/
theorem frobenius_certificates :
    modulus ∣ frobeniusPolynomial 64 - X ∧
      modulus ∣ frobeniusPolynomial 32 - remainder32 := by
  exact ⟨by simpa only [remainderAt, remainder64] using
    every_frobenius_certificate 64 (by decide),
    by simpa only [remainderAt] using every_frobenius_certificate 32 (by decide)⟩

/-- Direct Bézout certificate; independent of any irreducibility assumption. -/
theorem remainder32_coprime : IsCoprime modulus (remainder32 + X) := by
  exact ⟨_, _, bezout_certificate⟩

theorem modulus_monic : modulus.Monic := by
  unfold modulus
  monicity <;> norm_num

theorem modulus_natDegree : modulus.natDegree = 64 := by
  unfold modulus
  compute_degree <;> norm_num

private theorem small_divisor_of_64_divides_32 {degree : Nat}
    (positive : 0 < degree) (small : degree ≤ 32) (divides : degree ∣ 64) :
    degree ∣ 32 := by
  interval_cases degree <;> norm_num at *

/-- The exact native modulus is irreducible over the two-element coefficient field. -/
theorem modulus_irreducible : Irreducible modulus := by
  have not_one : modulus ≠ 1 := by
    intro equal
    have := congrArg Polynomial.natDegree equal
    rw [modulus_natDegree, natDegree_one] at this
    contradiction
  apply (modulus_monic.irreducible_iff_lt_natDegree_lt not_one).mpr
  intro divisor monic degrees divides
  rw [Finset.mem_Ioc, modulus_natDegree] at degrees
  obtain ⟨factor, irreducible, factor_divides⟩ :=
    exists_irreducible_of_natDegree_pos degrees.1
  have factor_divides_modulus := dvd_trans factor_divides divides
  obtain ⟨power64, power32⟩ := frobenius_certificates
  have factor_degree_divides_64 : factor.natDegree ∣ 64 := by
    exact (factor_degree_criterion irreducible 64).mpr
      (dvd_trans factor_divides_modulus power64)
  have factor_small : factor.natDegree ≤ 32 :=
    (natDegree_le_of_dvd factor_divides monic.ne_zero).trans degrees.2
  have factor_degree_divides_32 := small_divisor_of_64_divides_32
    irreducible.natDegree_pos factor_small factor_degree_divides_64
  have factor_divides_power32 : factor ∣ frobeniusPolynomial 32 - X := by
    exact (factor_degree_criterion irreducible 32).mp factor_degree_divides_32
  have factor_divides_difference :=
    dvd_sub (dvd_trans factor_divides_modulus power32) factor_divides_power32
  have factor_divides_remainder : factor ∣ remainder32 + X := by
    have reordered : factor ∣ X - remainder32 := by
      convert factor_divides_difference using 1; ring
    simpa only [CharTwo.sub_eq_add, add_comm] using reordered
  exact irreducible.not_isUnit
    (remainder32_coprime.isUnit_of_dvd' factor_divides_modulus factor_divides_remainder)

/-- Frozen literal-polynomial endpoint. -/
theorem exactPolynomialIrreducible : ModulusChallenges.exactPolynomialIrreducible :=
  modulus_irreducible

end BulksketchBridge.Algebra.Gf64
