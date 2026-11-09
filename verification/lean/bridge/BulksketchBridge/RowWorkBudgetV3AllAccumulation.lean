import BulksketchBridge.RowWorkBudgetV3FinalCharge
import BulksketchBridge.RowWorkBudgetV3ReserveExit
import BulksketchBridge.ClosedLeafAdvance
import BulksketchBridge.AffineSelector

namespace BulksketchBridge.RootWorkBudget

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work bulksketch.types
open core.result.Result.Insts
open AffineSelector (word word_val)

set_option maxRecDepth 4096
set_option maxHeartbeats 3400000
set_option linter.unusedSimpArgs false

private theorem addNormal (left right : U64) (fits : left.val + right.val ≤ U64.max) :
    add left right = .ok (.Ok (word (left.val + right.val))) :=
  (BmPrice.add_refines left right).trans (congrArg Result.ok
    ((checked_cost_ok_iff ..).mpr ⟨fits, word_val _ fits⟩))

private theorem mulNormal (left right : U64) (fits : left.val * right.val ≤ U64.max) :
    mul left right = .ok (.Ok (word (left.val * right.val))) :=
  (mul_refines left right).trans (congrArg Result.ok
    ((checked_cost_ok_iff ..).mpr ⟨fits, word_val _ fits⟩))

def ActualNativeV3AllAccumulation : Prop :=
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
    let affine := if 3#usize ≤ degree then
      setup.val + max enumeration.val (degree.val * (degree.val - 2) * split.val) else 0
    let three := if 3#usize ≤ capacity ∧ 3#usize ≤ budget then 863 + original.val else 0
    let four := if 4#usize ≤ capacity ∧ 4#usize ≤ budget then 2337 + original.val else 0
    let leaves := 671 * (budget.val / 3) + 2097 * (budget.val / 4)
    affine ≤ U64.max → three ≤ U64.max → four ≤ U64.max → leaves ≤ U64.max →
    WorkScheduleV3.row_bound sumCosts capacity budget beta candidates = .ok (checkedCost units)

theorem native_v3_all_accumulation : ActualNativeV3AllAccumulation := by
  intro sumCosts capacity budget beta candidates base original rebuilt setup enumeration split
    v2 verify rebuild degree rank affinePrices units affine three four leaves affineFits threeFits fourFits leafFits
  let delta := max rebuilt.val original.val - original.val
  let attempts := degree.val * (degree.val - 2)
  let splitting := attempts * split.val
  let first := base.val + delta
  let second := first + affine
  let third := second + three
  let fourth := third + four
  have totalValue : units = fourth + leaves := rfl
  by_cases fourthFits : fourth ≤ U64.max
  · exact native_v3_final_charge sumCosts capacity budget beta candidates base original rebuilt setup enumeration split
      v2 verify rebuild affinePrices leafFits (by
        change fourth + leaves - leaves ≤ U64.max
        rwa [Nat.add_sub_cancel])
  have totalError : checkedCost units = .Err .WorkLimitExceeded := by
    rw [checkedCost, dite_eq_right (by rw [totalValue]; omega)]
  by_cases firstFails : ¬ first ≤ U64.max
  · rw [totalError]
    exact native_v3_verifier_reserve_exit sumCosts capacity budget beta candidates base original rebuilt
      v2 verify rebuild (by change U64.max < first; omega)
  have firstFits : first ≤ U64.max := by omega
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
  have thirdPaid (prior : second ≤ U64.max) (room : third ≤ U64.max) :
      add (word second) (word three) = .ok (.Ok (word third)) := by
    simpa only [word_val second prior, word_val three threeFits, third] using
      addNormal (word second) (word three)
        (by rw [word_val second prior, word_val three threeFits]; exact room)
  have thirdDenied (prior : second ≤ U64.max) (overflow : ¬ third ≤ U64.max) :
      add (word second) (word three) = .ok (.Err .WorkLimitExceeded) := by
    rw [BmPrice.add_refines, word_val second prior, word_val three threeFits,
      checkedCost, dite_eq_right overflow]

  have fourCall (cap : 4#usize ≤ capacity) (bud : 4#usize ≤ budget) :
      add 2337#u64 original = .ok (.Ok (word four)) := by
    have exactFour : four = 2337 + original.val := by simp only [four, cap, bud, and_self, ite_true]
    rw [exactFour]
    exact addNormal _ _ (by change 2337 + original.val ≤ _; rwa [exactFour] at fourFits)
  have fourthDenied (prior : third ≤ U64.max) (overflow : ¬ fourth ≤ U64.max) :
      add (word third) (word four) = .ok (.Err .WorkLimitExceeded) := by
    rw [BmPrice.add_refines, word_val third prior, word_val four fourFits,
      checkedCost, dite_eq_right overflow]

  have maximum : bulksketch.decode.affine.MAX_PREFERRED_DEGREE = .ok 18#usize :=
    native_max_preferred_degree
  dsimp only [high] at subCall
  have affineOn : 3#usize ≤ degree := by
    by_contra! off
    have degreeSmall : degree.val < 3 := by
      rw [UScalar.lt_equiv] at off
      exact off
    have budgetSmall : budget.val < 3 := by rw [degreeValue] at degreeSmall; omega
    have noThree : ¬ 3#usize ≤ budget := by
      rw [UScalar.le_equiv]
      change ¬ 3 ≤ budget.val
      omega
    have noFour : ¬ 4#usize ≤ budget := by
      rw [UScalar.le_equiv]
      change ¬ 4 ≤ budget.val
      omega
    have idle : fourth = first := by
      simp only [fourth, third, second, four, three, affine, not_le_of_gt off, noThree, noFour,
        and_false, ite_false, Nat.add_zero]
    exact fourthFits (idle.symm ▸ firstFits)
  have live : 3 ≤ degree.val := by
    rw [UScalar.le_equiv] at affineOn
    exact affineOn
  have affineExact : affine = setup.val + max enumeration.val splitting := by
    simp only [affine, affineOn, ite_true, splitting, attempts]
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
  have secondPaid (prior : first ≤ U64.max) (room : second ≤ U64.max) :
      add (word first) (word affine) = .ok (.Ok (word second)) := by
    simpa only [word_val first prior, word_val affine affineFits, second] using
      addNormal (word first) (word affine)
        (by rw [word_val first prior, word_val affine affineFits]; exact room)
  have secondDenied (prior : first ≤ U64.max) (overflow : ¬ second ≤ U64.max) :
      add (word first) (word affine) = .ok (.Err .WorkLimitExceeded) := by
    rw [BmPrice.add_refines, word_val first prior, word_val affine affineFits,
      checkedCost, dite_eq_right overflow]
  dsimp only [degree] at affineOn setupCall rankSub enumCall splitCall degreeCall degreeSub
  dsimp only [highAffine] at affineCall
  rw [totalError]
  by_cases secondFails : ¬ second ≤ U64.max
  · have secondCall := secondDenied firstFits secondFails
    simp only [WorkScheduleV3.row_bound, v2, verify, rebuild, lift, bind_ok, CoreOpsTry.branch,
      subCall, firstCall, maximum, affineOn, ite_true, setupCall, rankSub, enumCall, splitCall,
      degreeCall, degreeSub, lessCall, attemptsCall, splitCall', affineCall, secondCall,
      CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    exact bind_ok _ _
  have secondFits : second ≤ U64.max := by omega
  have secondCall := secondPaid firstFits secondFits
  by_cases thirdFails : ¬ third ≤ U64.max
  · have enabled : 3#usize ≤ capacity ∧ 3#usize ≤ budget := by
      by_contra off
      exact thirdFails (by simpa only [third, three, off, ite_false, Nat.add_zero] using secondFits)
    have thirdCall := thirdDenied secondFits thirdFails
    simp only [WorkScheduleV3.row_bound, v2, verify, rebuild, lift, bind_ok, CoreOpsTry.branch,
      subCall, firstCall, maximum, affineOn, ite_true, setupCall, rankSub, enumCall, splitCall,
      degreeCall, degreeSub, lessCall, attemptsCall, splitCall', affineCall, secondCall,
      enabled.1, enabled.2, threeCall enabled.1 enabled.2, thirdCall,
      CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    exact bind_ok _ _
  have thirdFits : third ≤ U64.max := by omega
  have enabledFour : 4#usize ≤ capacity ∧ 4#usize ≤ budget := by
    by_contra off
    exact fourthFits (by simpa only [fourth, four, off, ite_false, Nat.add_zero] using thirdFits)
  have enabledThree : 3#usize ≤ capacity ∧ 3#usize ≤ budget := by
    obtain ⟨cap, size⟩ := enabledFour
    simp only [UScalar.le_equiv] at cap size ⊢
    change 4 ≤ capacity.val at cap
    change 4 ≤ budget.val at size
    change 3 ≤ capacity.val ∧ 3 ≤ budget.val
    omega
  have thirdCall := thirdPaid secondFits thirdFits
  have fourthCall := fourthDenied thirdFits fourthFits
  simp only [WorkScheduleV3.row_bound, v2, verify, rebuild, lift, bind_ok, CoreOpsTry.branch,
    subCall, firstCall, maximum, affineOn, ite_true, setupCall, rankSub, enumCall, splitCall,
    degreeCall, degreeSub, lessCall, attemptsCall, splitCall', affineCall, secondCall,
    enabledThree.1, enabledThree.2, threeCall enabledThree.1 enabledThree.2, thirdCall,
    enabledFour.1, enabledFour.2, fourCall enabledFour.1 enabledFour.2, fourthCall,
    CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  exact bind_ok _ _

#print axioms native_v3_all_accumulation

end BulksketchBridge.RootWorkBudget
