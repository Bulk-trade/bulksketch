import BulksketchBridge.RowWorkBudgetV3Prefix
import BulksketchBridge.ClosedLeafAdvance
import BulksketchBridge.AffineSelector

namespace BulksketchBridge.RootWorkBudget

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work bulksketch.types
open core.result.Result.Insts
open AffineSelector (word word_val)

set_option maxRecDepth 4096
set_option maxHeartbeats 3800000
set_option linter.unusedSimpArgs false

private theorem addNormal (left right : U64) (fits : left.val + right.val ≤ U64.max) :
    add left right = .ok (.Ok (word (left.val + right.val))) :=
  (BmPrice.add_refines left right).trans (congrArg Result.ok
    ((checked_cost_ok_iff ..).mpr ⟨fits, word_val _ fits⟩))

private theorem mulNormal (left right : U64) (fits : left.val * right.val ≤ U64.max) :
    mul left right = .ok (.Ok (word (left.val * right.val))) :=
  (mul_refines left right).trans (congrArg Result.ok
    ((checked_cost_ok_iff ..).mpr ⟨fits, word_val _ fits⟩))

/-- Exact natural subtotal with each source reserve gate represented explicitly. -/
def v3AdmittedUnits (capacity budget degree : Usize) (base original rebuilt setup enumeration split : U64) : Nat :=
  base.val + (max rebuilt.val original.val - original.val) +
    (if 3#usize ≤ degree then setup.val + max enumeration.val (degree.val * (degree.val - 2) * split.val) else 0) +
    (if 3#usize ≤ capacity ∧ 3#usize ≤ budget then 863 + original.val else 0) +
    (if 4#usize ≤ capacity ∧ 4#usize ≤ budget then 2337 + original.val else 0) +
    (671 * (budget.val / 3) + 2097 * (budget.val / 4))

def ActualNativeV3AdmittedRowBound : Prop :=
  ∀ (sumCosts : RowWorkBudgetRuntime.SumCosts) (capacity budget beta candidates : Usize)
    (base original rebuilt setup enumeration split : U64),
    WorkScheduleV2.row_bound sumCosts capacity budget beta candidates = .ok (.Ok base) →
    WorkScheduleV1.cost (.Verify capacity beta) = .ok (.Ok original) →
    WorkScheduleV1.cost (.VerifyLfsr capacity beta budget) = .ok (.Ok rebuilt) →
    let degree := core.cmp.impls.OrdUsize.min budget 18#usize
    let rank := ClosedLeafAdvance.usizeWord (degree.val - 1)
    (3#usize ≤ degree →
      WorkScheduleV1.cost (.AffinePreparation degree) = .ok (.Ok setup) ∧
      WorkScheduleV1.cost (.AffineEnumeration degree rank) = .ok (.Ok enumeration) ∧
      WorkScheduleV1.cost (.AffineSplit degree rank) = .ok (.Ok split)) →
    let units := v3AdmittedUnits capacity budget degree base original rebuilt setup enumeration split
    units ≤ U64.max →
    WorkScheduleV3.row_bound sumCosts capacity budget beta candidates = .ok (.Ok (word units))

theorem native_v3_admitted_row_bound : ActualNativeV3AdmittedRowBound := by
  intro sumCosts capacity budget beta candidates base original rebuilt setup enumeration split
    v2 verify rebuild degree rank affinePrices units fits
  let delta := max rebuilt.val original.val - original.val
  let attempts := degree.val * (degree.val - 2)
  let splitting := attempts * split.val
  let affine := if 3#usize ≤ degree then setup.val + max enumeration.val splitting else 0
  let three := if 3#usize ≤ capacity ∧ 3#usize ≤ budget then 863 + original.val else 0
  let four := if 4#usize ≤ capacity ∧ 4#usize ≤ budget then 2337 + original.val else 0
  let leaves := 671 * (budget.val / 3) + 2097 * (budget.val / 4)
  let first := base.val + delta
  let second := first + affine
  let third := second + three
  let fourth := third + four
  have finalFits : fourth + leaves ≤ U64.max := fits
  have firstFits : first ≤ U64.max := by omega
  have secondFits : second ≤ U64.max := by omega
  have thirdFits : third ≤ U64.max := by omega
  have fourthFits : fourth ≤ U64.max := by omega
  have affineFits : affine ≤ U64.max := by unfold second at secondFits; omega
  have threeFits : three ≤ U64.max := by unfold third at thirdFits; omega
  have fourFits : four ≤ U64.max := by unfold fourth at fourthFits; omega
  have leafFits : leaves ≤ U64.max := by omega
  have degreeValue : degree.val = min budget.val 18 := by
    simp only [degree, core.cmp.impls.OrdUsize.min_val, show (18#usize).val = 18 from rfl]
  have degreeMax : degree.val ≤ 18 := by rw [degreeValue]; omega
  have platformCap : 18 ≤ Usize.max := by
    simp only [Usize.max, Usize.numBits, UScalarTy.numBits]
    rcases System.Platform.numBits_eq with platform | platform <;> rw [platform] <;> decide
  let high := core.cmp.impls.OrdU64.max rebuilt original
  have highValue : high.val = max rebuilt.val original.val := by
    simp only [high, core.cmp.impls.OrdU64.max_val]
  obtain ⟨difference, subCall, subValue, _⟩ := RawMulTable.normal_of_spec _ _
    (U64.sub_spec (x := high) (y := original) (by rw [highValue]; exact Nat.le_max_right ..))
  have differenceValue : difference.val = delta := by rw [subValue, highValue]
  have firstCall : add base difference = .ok (.Ok (word first)) := by
    simpa only [first, differenceValue] using addNormal base difference
      (by rw [differenceValue]; exact firstFits)
  have threeCall (cap : 3#usize ≤ capacity) (bud : 3#usize ≤ budget) :
      add 863#u64 original = .ok (.Ok (word three)) := by
    have exactThree : three = 863 + original.val := by simp only [three, cap, bud, and_self, ite_true]
    rw [exactThree]
    exact addNormal _ _ (by change 863 + original.val ≤ _; rwa [exactThree] at threeFits)
  have thirdCall : add (word second) (word three) = .ok (.Ok (word third)) := by
    simpa only [word_val second secondFits, word_val three threeFits, third] using
      addNormal (word second) (word three)
        (by rw [word_val second secondFits, word_val three threeFits]; exact thirdFits)
  have fourCall (cap : 4#usize ≤ capacity) (bud : 4#usize ≤ budget) :
      add 2337#u64 original = .ok (.Ok (word four)) := by
    have exactFour : four = 2337 + original.val := by simp only [four, cap, bud, and_self, ite_true]
    rw [exactFour]
    exact addNormal _ _ (by change 2337 + original.val ≤ _; rwa [exactFour] at fourFits)
  have fourthCall : add (word third) (word four) = .ok (.Ok (word fourth)) := by
    simpa only [word_val third thirdFits, word_val four fourFits, fourth] using
      addNormal (word third) (word four)
        (by rw [word_val third thirdFits, word_val four fourFits]; exact fourthFits)
  have skipThree (off : ¬ (3#usize ≤ capacity ∧ 3#usize ≤ budget)) : word second = word third := by
    simp only [third, three, off, ite_false, Nat.add_zero]
  have skipFour (off : ¬ (4#usize ≤ capacity ∧ 4#usize ≤ budget)) : word third = word fourth := by
    simp only [fourth, four, off, ite_false, Nat.add_zero]
  obtain ⟨thirdBudget, divThree, thirdBudgetValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.div_spec budget (y := 3#usize) (by decide))
  obtain ⟨fourthBudget, divFour, fourthBudgetValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.div_spec budget (y := 4#usize) (by decide))
  change thirdBudget.val = budget.val / 3 at thirdBudgetValue
  change fourthBudget.val = budget.val / 4 at fourthBudgetValue
  obtain ⟨thirdWord, thirdBudgetCall, thirdWordValue⟩ := number_refines thirdBudget
  obtain ⟨fourthWord, fourthBudgetCall, fourthWordValue⟩ := number_refines fourthBudget
  let leafThree := 671 * (budget.val / 3)
  let leafFour := 2097 * (budget.val / 4)
  have leafThreeFits : leafThree ≤ U64.max := by unfold leaves at leafFits; omega
  have leafFourFits : leafFour ≤ U64.max := by unfold leaves at leafFits; omega
  have leafThreeCall : mul 671#u64 thirdWord = .ok (.Ok (word leafThree)) := by
    simpa only [thirdWordValue, thirdBudgetValue, leafThree, show (671#u64).val = 671 from rfl] using
      mulNormal 671#u64 thirdWord (by rw [thirdWordValue, thirdBudgetValue]; exact leafThreeFits)
  have leafFourCall : mul 2097#u64 fourthWord = .ok (.Ok (word leafFour)) := by
    simpa only [fourthWordValue, fourthBudgetValue, leafFour, show (2097#u64).val = 2097 from rfl] using
      mulNormal 2097#u64 fourthWord (by rw [fourthWordValue, fourthBudgetValue]; exact leafFourFits)
  have leavesCall : add (word leafThree) (word leafFour) = .ok (.Ok (word leaves)) := by
    simpa only [word_val leafThree leafThreeFits, word_val leafFour leafFourFits, leaves, leafThree, leafFour] using
      addNormal (word leafThree) (word leafFour)
        (by rw [word_val leafThree leafThreeFits, word_val leafFour leafFourFits]; exact leafFits)
  have finalCall : add (word fourth) (word leaves) = .ok (.Ok (word units)) := by
    change add (word fourth) (word leaves) = .ok (.Ok (word (fourth + leaves)))
    simpa only [word_val fourth fourthFits, word_val leaves leafFits] using
      addNormal (word fourth) (word leaves)
        (by rw [word_val fourth fourthFits, word_val leaves leafFits]; exact finalFits)
  have maximum : bulksketch.decode.affine.MAX_PREFERRED_DEGREE = .ok 18#usize :=
    native_max_preferred_degree
  dsimp only [high] at subCall
  by_cases affineOn : 3#usize ≤ degree
  ·
    have live : 3 ≤ degree.val := by
      rw [UScalar.le_equiv] at affineOn
      exact affineOn
    have affineExact : affine = setup.val + max enumeration.val splitting := by
      simp only [affine, affineOn, ite_true]
    have rawAffineFits : setup.val + max enumeration.val splitting ≤ U64.max := affineExact ▸ affineFits
    have splitFits : splitting ≤ U64.max :=
      (Nat.le_max_right enumeration.val splitting).trans ((Nat.le_add_left _ _).trans rawAffineFits)
    obtain ⟨setupCall, enumCall, splitCall⟩ := affinePrices affineOn
    have attemptsFits : attempts ≤ U64.max := by
      have upper : degree.val * (degree.val - 2) ≤ 18 * 16 := Nat.mul_le_mul degreeMax (by omega)
      rw [U64.max_eq]
      exact upper.trans (by decide)
    obtain ⟨lessOne, rankSub, rankValue, _⟩ := RawMulTable.normal_of_spec _ _
      (Usize.sub_spec (x := degree) (y := 1#usize) (by exact Nat.le_of_succ_le (by omega : 2 ≤ degree.val)))
    have rankEq : lessOne = rank := UScalar.eq_of_val_eq (by
      change lessOne.val = (ClosedLeafAdvance.usizeWord (degree.val - 1)).val
      rw [ClosedLeafAdvance.word_val _ ((Nat.sub_le ..).trans (degreeMax.trans platformCap))]
      exact rankValue)
    rw [rankEq] at rankSub
    obtain ⟨lessTwo, degreeSub, lessValue, _⟩ := RawMulTable.normal_of_spec _ _
      (Usize.sub_spec (x := degree) (y := 2#usize) (by change 2 ≤ degree.val; omega))
    change lessTwo.val = degree.val - 2 at lessValue
    obtain ⟨degreeWord, degreeCall, degreeWordValue⟩ := number_refines degree
    obtain ⟨lessWord, lessCall, lessWordValue⟩ := number_refines lessTwo
    have attemptsCall : mul degreeWord lessWord = .ok (.Ok (word attempts)) := by
      simpa only [degreeWordValue, lessWordValue, lessValue, attempts] using
        mulNormal degreeWord lessWord (by rw [degreeWordValue, lessWordValue, lessValue]; exact attemptsFits)
    have splitCall' : mul (word attempts) split = .ok (.Ok (word splitting)) := by
      simpa only [word_val attempts attemptsFits, splitting] using mulNormal (word attempts) split
        (by rw [word_val attempts attemptsFits]; exact splitFits)
    let highAffine := core.cmp.impls.OrdU64.max enumeration (word splitting)
    have highAffineValue : highAffine.val = max enumeration.val splitting := by
      simp only [highAffine, core.cmp.impls.OrdU64.max_val, word_val splitting splitFits]
    have affineCall : add setup highAffine = .ok (.Ok (word affine)) := by
      simpa only [highAffineValue, affineExact] using addNormal setup highAffine
        (by rw [highAffineValue]; exact rawAffineFits)
    have secondCall : add (word first) (word affine) = .ok (.Ok (word second)) := by
      simpa only [word_val first firstFits, word_val affine affineFits, second] using
        addNormal (word first) (word affine)
          (by rw [word_val first firstFits, word_val affine affineFits]; exact secondFits)
    dsimp only [degree] at affineOn setupCall rankSub enumCall splitCall degreeCall degreeSub
    dsimp only [highAffine] at affineCall
    simp only [WorkScheduleV3.row_bound, v2, verify, rebuild, lift, bind_ok, CoreOpsTry.branch,
      subCall, firstCall, maximum, affineOn, ite_true, setupCall, rankSub, enumCall, splitCall,
      degreeCall, degreeSub, lessCall, attemptsCall, splitCall', affineCall, secondCall]
    by_cases capThree : 3#usize ≤ capacity <;> by_cases budThree : 3#usize ≤ budget <;>
      by_cases capFour : 4#usize ≤ capacity <;> by_cases budFour : 4#usize ≤ budget
    all_goals
      try
        have noThree : ¬ (3#usize ≤ capacity ∧ 3#usize ≤ budget) := by
          rintro ⟨cap, size⟩
          contradiction
      try
        have noFour : ¬ (4#usize ≤ capacity ∧ 4#usize ≤ budget) := by
          rintro ⟨cap, size⟩
          contradiction
      simp (disch := assumption) only
        [capThree, budThree, capFour, budFour, ite_true, ite_false, and_self, false_and, and_false,
          threeCall, thirdCall, fourCall, fourthCall, skipThree, skipFour,
          divThree, divFour, thirdBudgetCall, fourthBudgetCall,
          leafThreeCall, leafFourCall, leavesCall, finalCall, bind_ok, CoreOpsTry.branch]
  · have idleAffine : word first = word second := by simp only [second, affine, affineOn, ite_false, Nat.add_zero]
    dsimp only [degree] at affineOn
    simp only [WorkScheduleV3.row_bound, v2, verify, rebuild, lift, bind_ok, CoreOpsTry.branch,
      subCall, firstCall, maximum, affineOn, ite_false, idleAffine]
    by_cases capThree : 3#usize ≤ capacity <;> by_cases budThree : 3#usize ≤ budget <;>
      by_cases capFour : 4#usize ≤ capacity <;> by_cases budFour : 4#usize ≤ budget
    all_goals
      try
        have noThree : ¬ (3#usize ≤ capacity ∧ 3#usize ≤ budget) := by
          rintro ⟨cap, size⟩
          contradiction
      try
        have noFour : ¬ (4#usize ≤ capacity ∧ 4#usize ≤ budget) := by
          rintro ⟨cap, size⟩
          contradiction
      simp (disch := assumption) only
        [capThree, budThree, capFour, budFour, ite_true, ite_false, and_self, false_and, and_false,
          threeCall, thirdCall, fourCall, fourthCall, skipThree, skipFour,
          divThree, divFour, thirdBudgetCall, fourthBudgetCall,
          leafThreeCall, leafFourCall, leavesCall, finalCall, bind_ok, CoreOpsTry.branch]

#print axioms native_v3_admitted_row_bound

end BulksketchBridge.RootWorkBudget
