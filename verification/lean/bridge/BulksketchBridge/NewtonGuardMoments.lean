import BulksketchBridge.NewtonGuardMomentSpec
import BulksketchBridge.NewtonGuardResidual
import BulksketchBridge.SyndromeUniqueness
import BulksketchBridge.Algebra.Word

namespace BulksketchBridge.NewtonGuard

open Aeneas.Std Algebra.Gf64 Reconciliation NewtonGuardResidual
open scoped BigOperators

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

private theorem observed_power (roots : Finset Field) (odd : Slice U64) (power : Nat)
    (row : OddMoments roots odd) (positive : 1 ≤ power) (small : power < 16)
    (inRow : observationIndex power < odd.length) :
    value (observedWord odd power) = powerSum roots power := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  have word : toField odd[observationIndex power]!.bv = oddSyndrome roots (observationIndex power) :=
    row _ inRow
  change toField (BulksketchProofs.Field.Period.iterateSquare (squaresFor power)
    odd[observationIndex power]!.bv) = _
  calc
    _ = powerSum roots (2 * observationIndex power + 1) ^ (2 ^ squaresFor power) := by
      rw [toField_iterateSquare, word, oddSyndrome]
    _ = powerSum roots ((2 * observationIndex power + 1) * 2 ^ squaresFor power) := by
      simp only [powerSum, sum_pow_char_pow, pow_mul]
    _ = _ := congrArg (powerSum roots) (power_decomposition power positive small)

private theorem residualFrom_field (odd cleared : Slice U64)
    (degree exponent lag : Nat) (accumulator : U64) (count : Nat) :
    value (residualFrom odd cleared degree exponent lag accumulator count) =
      value accumulator + ∑ offset ∈ Finset.range count,
        value cleared[degree - (lag + offset)]! * value (observedWord odd (exponent - (lag + offset))) := by
  induction count generalizing lag accumulator with
  | zero => simp [residualFrom]
  | succ count ih =>
    rw [residualFrom, ih, Finset.sum_range_succ']
    have term : value (accumulator ^^^ lagTerm odd cleared degree exponent lag) =
        value accumulator + value cleared[degree - lag]! * value (observedWord odd (exponent - lag)) := by
      calc
        _ = value accumulator + value (lagTerm odd cleared degree exponent lag) := toField_xor _ _
        _ = _ := congrArg (value accumulator + ·) (toField_mul _ _)
    rw [term]
    simp only [Nat.add_zero]
    have ordered (offset : Nat) : lag + 1 + offset = lag + (offset + 1) := by omega
    simp only [ordered]
    ac_rfl

theorem residual_value (roots : Finset Field) (odd cleared : Slice U64) (denominator : U64)
    (degree index : Nat) (degrees : degree = 3 ∨ degree = 4) (row : OddMoments roots odd)
    (first : degree ≤ index) (last : index < min odd.length (degree + 2)) :
    value (residualWord odd cleared denominator degree index) =
      momentResidual roots cleared denominator degree index := by
  have indexBound : index < odd.length := (Nat.lt_min.mp last).1
  have indexLimit : index < degree + 2 := (Nat.lt_min.mp last).2
  rw [residualWord, residualFrom_field, momentResidual]
  have initial : value (NewtonGuardResidual.mulWord denominator odd[index]!) =
      value denominator * powerSum roots (2 * index + 1) := by
    rw [← oddSyndrome, ← row index indexBound]
    exact toField_mul _ _
  rw [initial]
  apply congrArg (value denominator * powerSum roots (2 * index + 1) + ·)
  apply Finset.sum_congr rfl
  intro offset member
  have lagBound := Finset.mem_range.mp member
  have bounds : 1 ≤ 2 * index + 1 - (1 + offset) ∧ 2 * index + 1 - (1 + offset) < 16 := by omega
  have observedBound : observationIndex (2 * index + 1 - (1 + offset)) < odd.length := by
    unfold observationIndex
    have shifted := Nat.shiftRight_le (2 * index + 1 - (1 + offset))
      (squaresFor (2 * index + 1 - (1 + offset)))
    omega
  rw [observed_power roots odd _ row bounds.1 bounds.2 observedBound]
  simp only [Nat.add_comm 1 offset]

theorem residual_moment_meaning : ResidualMomentMeaning := by
  intro roots odd cleared denominator degree degrees row
  rw [residualOK, residualChecks_true_iff]
  constructor
  · intro checks index first last
    have tested := checks (index - degree) (by omega)
    rw [show degree + (index - degree) = index by omega] at tested
    have moment := residual_value roots odd cleared denominator degree index degrees row first last
    rw [← moment, tested]
    exact toField_zero
  · intro checks offset bounded
    have first : degree ≤ degree + offset := by omega
    have last : degree + offset < min odd.length (degree + 2) := by omega
    have moment := residual_value roots odd cleared denominator degree (degree + offset) degrees row first last
    apply U64.bv_eq_imp_eq
    apply toField_injective
    exact moment.trans ((checks (degree + offset) first last).trans toField_zero.symm)

end BulksketchBridge.NewtonGuard
