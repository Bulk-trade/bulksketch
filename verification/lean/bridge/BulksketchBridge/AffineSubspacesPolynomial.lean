import BulksketchBridge.AffineSubspacesCoefficients
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Coeff

namespace BulksketchBridge.AffineSubspaces

open Aeneas Aeneas.Std
open AffineLinearEval Algebra.Gf64 Polynomial
open bulksketch.backend.contract
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

/-- Interpret row position i as the coefficient at the exponent 2^i. -/
noncomputable def rowPolynomial (words : Slice U64) : Polynomial Field :=
  ∑ i ∈ Finset.range words.length, C (toField words[i]!.bv) * X ^ (2 ^ i)

theorem rowPolynomial_eval (words : Slice U64) (direction : U64) :
    (rowPolynomial words).eval (toField direction.bv) = linearValueFrom words direction 0 := by
  simp only [rowPolynomial, linearValueFrom, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    Nat.sub_zero, Nat.zero_add]

theorem tableStep_polynomial {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (table updated : Slice U64) (rank : Nat)
    (direction : U64) (room : offset (rank + 1 + 1) ≤ table.length)
    (ran : tableStep kernels table rank direction = .ok updated) :
    rowPolynomial (row updated (rank + 1)) =
      (rowPolynomial (row table rank)) ^ 2 +
        C ((rowPolynomial (row table rank)).eval (toField direction.bv)) * rowPolynomial (row table rank) := by
  obtain ⟨sameLength, coefficients, _⟩ :=
    tableStep_coefficients kernels arithmetic table updated rank direction room ran
  have previousSize := row_length table rank ((offset_mono (by omega)).trans room)
  have nextSize := row_length updated (rank + 1) (by rwa [sameLength])
  let previous := row table rank
  let value := linearValueFrom previous direction 0
  let scaled : Nat → Field := fun i => if i < rank + 1 then value * toField previous[i]!.bv else 0
  let squared : Nat → Field := fun i => if 0 < i ∧ i ≤ rank + 1 then toField previous[i - 1]!.bv ^ 2 else 0
  have exactSum : rowPolynomial (row updated (rank + 1)) =
      (∑ i ∈ Finset.range (rank + 2), C (scaled i) * X ^ (2 ^ i)) +
      (∑ i ∈ Finset.range (rank + 2), C (squared i) * X ^ (2 ^ i)) := by
    simp only [rowPolynomial, nextSize, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [coefficients i (Finset.mem_range.mp hi)]
    change C (scaled i + squared i) * _ = _
    rw [map_add, add_mul]
  have scaleSum : (∑ i ∈ Finset.range (rank + 2), C (scaled i) * X ^ (2 ^ i)) =
      C value * rowPolynomial previous := by
    rw [Finset.sum_range_succ, show scaled (rank + 1) = 0 by simp [scaled], map_zero, zero_mul, add_zero]
    rw [rowPolynomial, show previous.length = rank + 1 from previousSize, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [scaled, Finset.mem_range.mp hi, ite_true, map_mul, mul_assoc]
  have squareSum : (∑ i ∈ Finset.range (rank + 2), C (squared i) * X ^ (2 ^ i)) =
      rowPolynomial previous ^ 2 := by
    rw [Finset.sum_range_succ', show squared 0 = 0 by simp [squared], map_zero, zero_mul, add_zero]
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [rowPolynomial, show previous.length = rank + 1 from previousSize,
      sum_pow_char (p := 2)]
    apply Finset.sum_congr rfl
    intro i hi
    have active : 0 < i + 1 ∧ i + 1 ≤ rank + 1 := by have := Finset.mem_range.mp hi; omega
    simp only [squared, active, true_and, ite_true, Nat.add_sub_cancel, C_pow, mul_pow, ← pow_mul, pow_succ (2 : Nat)]
  rw [exactSum, scaleSum, squareSum, rowPolynomial_eval, add_comm]

end BulksketchBridge.AffineSubspaces
