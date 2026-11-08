import BulksketchBridge.NewtonGuardSupportSpec
import BulksketchBridge.NewtonGuard
import BulksketchBridge.NewtonGuardMoments
import BulksketchBridge.ReconciliationLocator

namespace BulksketchBridge.NewtonGuard

open Aeneas.Std Algebra.Gf64 Reconciliation
open scoped BigOperators
open NewtonGuardResidual (residualOK)

private theorem residual_eq_locator_sum (roots : Finset Field) (cleared : Slice U64)
    (denominator : U64) (degree index : Nat) (size : roots.card = degree)
    (first : degree ≤ index)
    (coefficients : ∀ term < degree,
      value cleared[term]! = value denominator * (supportLocator roots).coeff term) :
    momentResidual roots cleared denominator degree index =
      value denominator * positiveRecurrenceSum roots (supportLocator roots) (2 * index + 1 - degree) := by
  let locator := supportLocator roots
  let start := 2 * index + 1 - degree
  have degreeEq : locator.natDegree = degree := (supportLocator_natDegree roots).trans size
  have leading : locator.coeff degree = 1 := by
    rw [← degreeEq]
    exact (supportLocator_monic roots).coeff_natDegree
  have moment : start + degree = 2 * index + 1 := by dsimp [start]; omega
  have tails :
      (∑ offset ∈ Finset.range degree,
        value cleared[degree - (offset + 1)]! * powerSum roots (2 * index + 1 - (offset + 1))) =
      value denominator * ∑ term ∈ Finset.range degree, locator.coeff term * powerSum roots (start + term) := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro offset member
    have within := Finset.mem_range.mp member
    have slot : degree - (degree - 1 - offset + 1) = offset := by omega
    have power : 2 * index + 1 - (degree - 1 - offset + 1) = start + offset := by omega
    rw [coefficients _ (by omega), slot, power, mul_assoc]
  change _ = value denominator * positiveRecurrenceSum roots locator start
  rw [momentResidual, tails, positiveRecurrenceSum, degreeEq, Finset.sum_range_succ,
    leading, one_mul, moment, mul_add, add_comm]

theorem guard_accepts_support : ActualGuardAcceptsSupport := by
  intro K kernels roots odd scratch degree arithmetic admitted size row
  dsimp only
  intro nonzero coefficients
  have degrees : degree.val = 3 ∨ degree.val = 4 := by
    rcases admitted.degreeCases with three | four
    · left; rw [three]; rfl
    · right; rw [four]; rfl
  let words := clearedWords odd degree.val
  let updated := clearedFrame scratch words
  change words.2 ≠ 0#u64 at nonzero
  have accepted : residualOK odd updated words.2 degree.val = true := by
    apply (residual_moment_meaning roots odd updated words.2 degree.val degrees row).mpr
    intro index first _
    rw [residual_eq_locator_sum roots updated words.2 degree.val index size first coefficients]
    have start : 0 < 2 * index + 1 - degree.val := by omega
    have zero := supportLocator_recurs roots (2 * index + 1 - degree.val + (supportLocator roots).natDegree)
      (2 * index + 1 - degree.val) start (by rfl)
    rw [zero, mul_zero]
  rw [guard_refines kernels odd degree scratch arithmetic admitted]
  simp only [expected, ← show words = clearedWords odd degree.val from rfl, nonzero, ite_false, ← show
    updated = clearedFrame scratch words from rfl, accepted]

end BulksketchBridge.NewtonGuard
