import BulksketchBridge.RootAffinePreparationPrice
import BulksketchBridge.RootEnumeratePrice
import BulksketchBridge.AffineSelector

namespace BulksketchBridge.RootWorkBudget

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work
open AffineSelector (word word_val)
open ExecutionVerify (checkedNext)

def preparationUnits (degree : Nat) : Nat :=
  (5 * (degree * degree * degree) + 16 * (degree * degree)) + (327 * degree + 16900)

def enumerationUnits (degree rank : Nat) : Nat :=
  2 * 2 ^ rank * (degree + 2) + (degree + 1)

def splitterUnits (degree rank : Nat) : Nat :=
  rank * ((3 * (degree * degree) + 2 * degree) + (3 * degree + 3)) + (3 * degree + 1)

private theorem checkedWord (n : Nat) (fits : n ≤ U64.max) :
    checkedCost n = .Ok (word n) :=
  (checked_cost_ok_iff ..).mpr ⟨fits, word_val n fits⟩

private theorem checkedNextValue (n : Nat) (fits : n ≤ U64.max) (next : Nat → CostResult) :
    checkedNext n next = next n := by
  simp only [checkedNext, checkedWord n fits, word_val n fits]

def ActualNativeV3AffineQuotes : Prop :=
  ∀ (degree rank : Usize), degree.val ≤ 18 → rank.val ≤ 17 →
    WorkScheduleV1.cost (.AffinePreparation degree) = .ok (.Ok (word (preparationUnits degree.val))) ∧
    WorkScheduleV1.cost (.AffineEnumeration degree rank) = .ok (.Ok (word (enumerationUnits degree.val rank.val))) ∧
    WorkScheduleV1.cost (.AffineSplit degree rank) = .ok (.Ok (word (splitterUnits degree.val rank.val))) ∧
    preparationUnits degree.val +
      max (enumerationUnits degree.val rank.val)
        (degree.val * (degree.val - 2) * splitterUnits degree.val rank.val) ≤ U64.max

theorem native_v3_affine_quotes : ActualNativeV3AffineQuotes := by
  intro degree rank degreeMax rankMax
  let d := degree.val
  let r := rank.val
  have dMax : d ≤ 18 := degreeMax
  have rMax : r ≤ 17 := rankMax
  have square : d * d ≤ 324 := Nat.mul_le_mul dMax dMax
  have cube : d * d * d ≤ 5832 := Nat.mul_le_mul square dMax
  have points : 2 ^ r ≤ 131072 := Nat.pow_le_pow_right (by decide) rMax
  have evaluations : 2 * 2 ^ r * (d + 2) ≤ 5242880 := by
    exact (Nat.mul_le_mul (show 2 * 2 ^ r ≤ 262144 by omega) (show d + 2 ≤ 20 by omega)).trans (by decide)
  have splitRank : r * ((3 * (d * d) + 2 * d) + (3 * d + 3)) ≤ 18105 := by
    have oneRank : (3 * (d * d) + 2 * d) + (3 * d + 3) ≤ 1065 := by omega
    exact (Nat.mul_le_mul rMax oneRank).trans (by decide)
  have prepBound : preparationUnits d ≤ 57130 := by unfold preparationUnits; omega
  have enumBound : enumerationUnits d r ≤ 5242899 := by unfold enumerationUnits; omega
  have splitBound : splitterUnits d r ≤ 18160 := by unfold splitterUnits; omega
  have attempts : d * (d - 2) ≤ 288 :=
    (Nat.mul_le_mul dMax (show d - 2 ≤ 16 by omega)).trans (by decide)
  have attemptsCost : d * (d - 2) * splitterUnits d r ≤ 5230080 := Nat.mul_le_mul attempts splitBound
  have sumBound : preparationUnits d + max (enumerationUnits d r)
      (d * (d - 2) * splitterUnits d r) ≤ U64.max := by
    have larger : max (enumerationUnits d r) (d * (d - 2) * splitterUnits d r) ≤ 5242899 :=
      max_le enumBound (attemptsCost.trans (by decide))
    rw [U64.max_eq]
    omega
  refine ⟨?_, ?_, ?_, sumBound⟩
  · rw [RootRun.affine_preparation_cost_refines, RootRun.affinePreparationCost]
    change Result.ok (checkedNext (d * d) fun sq =>
      checkedNext (sq * d) fun cub =>
      checkedNext (5 * cub) fun cubic =>
      checkedNext (16 * sq) fun quadratic =>
      checkedNext (cubic + quadratic) fun elimination =>
      checkedNext (327 * d) fun linear =>
      checkedNext (linear + 16900) fun binaryMap =>
      checkedCost (elimination + binaryMap)) = _
    simp only [checkedNextValue (d * d) (by rw [U64.max_eq]; omega),
      checkedNextValue (d * d * d) (by rw [U64.max_eq]; omega),
      checkedNextValue (5 * (d * d * d)) (by rw [U64.max_eq]; omega),
      checkedNextValue (16 * (d * d)) (by rw [U64.max_eq]; omega),
      checkedNextValue (5 * (d * d * d) + 16 * (d * d)) (by rw [U64.max_eq]; omega),
      checkedNextValue (327 * d) (by rw [U64.max_eq]; omega),
      checkedNextValue (327 * d + 16900) (by rw [U64.max_eq]; omega)]
    change Result.ok (checkedCost (preparationUnits d)) = _
    rw [checkedWord _ (by rw [U64.max_eq]; omega)]
  · rw [RootEnumerate.enumeration_cost_refines, RootEnumerate.enumerationCost, ite_eq_left (by omega : rank.val < 64)]
    change Result.ok (checkedNext (2 * 2 ^ r) fun twice =>
      checkedNext (d + 2) fun width =>
      checkedNext (twice * width) fun evaluation =>
      checkedNext (d + 1) fun accepted =>
      checkedCost (evaluation + accepted)) = _
    simp only [checkedNextValue (2 * 2 ^ r) (by rw [U64.max_eq]; omega),
      checkedNextValue (d + 2) (by rw [U64.max_eq]; omega),
      checkedNextValue (2 * 2 ^ r * (d + 2)) (by rw [U64.max_eq]; omega),
      checkedNextValue (d + 1) (by rw [U64.max_eq]; omega)]
    change Result.ok (checkedCost (enumerationUnits d r)) = _
    rw [checkedWord _ (by rw [U64.max_eq]; omega)]
  · let sq := 3 * (d * d) + 2 * d
    have squarePrice : RootRun.squareModCost degree = .Ok (word sq) := by
      unfold RootRun.squareModCost
      change (checkedNext (d*d) fun square =>
        checkedNext (3 * square) fun quadratic =>
        checkedNext (2 * d) fun linear =>
        checkedCost (quadratic + linear)) = _
      simp only [checkedNextValue (d * d) (by rw [U64.max_eq]; omega),
        checkedNextValue (3 * (d * d)) (by rw [U64.max_eq]; omega),
        checkedNextValue (2 * d) (by rw [U64.max_eq]; omega)]
      change checkedCost sq = _
      exact checkedWord sq (by unfold sq; rw [U64.max_eq]; omega)
    rw [RootRun.affine_split_cost_refines, RootRun.affineSplitCost, squarePrice]
    have sqValue := word_val sq (by unfold sq; rw [U64.max_eq]; omega)
    simp only [sqValue]
    change Result.ok (checkedNext (3 * d) fun triple =>
      checkedNext (triple + 3) fun next =>
      checkedNext (sq + next) fun perRank =>
      checkedNext (r * perRank) fun allRanks =>
      checkedNext (triple + 1) fun fixed =>
      checkedCost (allRanks + fixed)) = _
    simp only [checkedNextValue (3 * d) (by rw [U64.max_eq]; omega),
      checkedNextValue (3 * d + 3) (by rw [U64.max_eq]; omega),
      checkedNextValue (sq + (3 * d + 3)) (by unfold sq; rw [U64.max_eq]; omega),
      checkedNextValue (r * (sq + (3 * d + 3))) (by unfold sq; rw [U64.max_eq]; omega),
      checkedNextValue (3 * d + 1) (by rw [U64.max_eq]; omega)]
    change Result.ok (checkedCost (splitterUnits d r)) = _
    rw [checkedWord _ (by rw [U64.max_eq]; omega)]

#print axioms native_v3_affine_quotes

end BulksketchBridge.RootWorkBudget
