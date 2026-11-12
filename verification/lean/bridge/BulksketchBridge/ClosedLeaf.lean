import BulksketchBridge.ClosedLeafPrices
import BulksketchBridge.StageCharge
import BulksketchBridge.QuarticSolve
import BulksketchBridge.Certificate

namespace BulksketchBridge.ClosedLeaf

open Aeneas Aeneas.Std Aeneas.Std.WP DenseCoefficient RebuiltLfsr
open bulksketch.types bulksketch.decode.roots bulksketch.decode.scratch bulksketch.backend.contract

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

private theorem stage_test (stage : Stage) :
    core.cmp.PartialEq.ne.trait_default bulksketch.types.Stage.Insts.CoreCmpPartialEqStage
      stage Stage.FactorVerification = .ok (!verifying stage) := by
  cases stage <;>
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      bulksketch.types.Stage.Insts.CoreCmpPartialEqStage.eq,
      verifying, bulksketch.types.Stage.read_discriminant]

theorem degree_values (roots : Roots) (degree : roots.degree = 3#usize ∨ roots.degree = 4#usize) :
    roots.degree.val = 3 ∨ roots.degree.val = 4 := by
  rcases degree with three | four
  · left; rw [three]; rfl
  · right; rw [four]; rfl

theorem factor_length (roots : Roots) (workspace : RowWorkspace)
    (degree : roots.degree.val = 3 ∨ roots.degree.val = 4)
    (room : 15 ≤ workspace.polynomials.length) :
    (factorWords roots workspace).length = roots.degree.val + 1 := by
  rw [factorWords, prefix_length, Nat.min_eq_left (by omega)]

private theorem solver_normal {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : Cubic.CorrectArithmetic kernels) (roots : Roots) (workspace : RowWorkspace)
    (degree : roots.degree.val = 3 ∨ roots.degree.val = 4) (room : 15 ≤ workspace.polynomials.length) :
    ∃ result, bulksketch.decode.deg34.solve fieldDictionary kernels (factorWords roots workspace)
      (region workspace.polynomials 11 15) = .ok result ∧ result.2.length = 4 := by
  have factorLen := factor_length roots workspace degree room
  have outputLen := region_length workspace.polynomials 11 15 room
  obtain ⟨result, normal, cubic, quartic⟩ := QuarticSolve.solve_refines kernels (factorWords roots workspace)
    (region workspace.polynomials 11 15) arithmetic (by omega) (by omega)
  refine ⟨result, normal, ?_⟩
  rcases degree with three | four
  · obtain ⟨candidates, _, exactFrame⟩ := cubic (by omega)
    rw [exactFrame]
    cases candidates <;> simp [QuarticSolve.expectedFrame, outputLen]
  · obtain ⟨candidates, _, exactFrame⟩ := quartic (by omega)
    rw [exactFrame]
    cases candidates <;> simp [QuarticSolve.expectedFrame, outputLen]

private theorem paid_solve {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : Cubic.CorrectArithmetic kernels)
    (roots : Roots) (stage : Stage) (workspace : RowWorkspace) (meter finalMeter : WorkMeter)
    (admitted : Admitted roots stage workspace) (phase : verifying stage = false)
    (chargeNormal : charge meter (leafOperation roots stage) = .ok (.Ok (), finalMeter)) :
    Roots.closed_leaf fieldDictionary kernels roots stage workspace meter = (do
      let result ← bulksketch.decode.deg34.solve fieldDictionary kernels (factorWords roots workspace)
        (region workspace.polynomials 11 15)
      .ok (solveFrame roots workspace finalMeter result)) := by
  have room := admitted.candidateRoom
  have degree := degree_values roots admitted.degree
  obtain ⟨rest, back, split, restVal, restLength, join⟩ :=
    split_normal workspace.polynomials 11#usize (by change 11 ≤ workspace.polynomials.length; omega)
  change rest.length = workspace.polynomials.length - 11 at restLength
  have factorBound : roots.degree.val < (prefixSlice workspace.polynomials 11).length := by
    rw [prefix_length]; omega
  have factorNormal := inclusive_prefix_normal (prefixSlice workspace.polynomials 11) roots.degree factorBound
  rw [prefix_prefix _ _ _ (by omega)] at factorNormal
  change core.slice.index.Slice.index (RebuiltLfsrRuntime.inclusive U64) _ ⟨roots.degree⟩ =
    Result.ok (factorWords roots workspace) at factorNormal
  have prefixNormal := prefix_normal rest 4#usize (by change 4 ≤ rest.length; omega)
  change _ = Result.ok (prefixSlice rest 4, restorePrefix rest) at prefixNormal
  rw [prefix_tail_region workspace.polynomials rest 11 4 restVal] at prefixNormal
  obtain ⟨⟨count, replacement⟩, solved, replacementLen⟩ := solver_normal kernels arithmetic roots workspace degree room
  change replacement.length = 4 at replacementLen
  have write := join replacement (by omega)
  change back (prefixSlice workspace.polynomials 11, restorePrefix rest replacement) =
    workspace.polynomials.setSlice! 11 replacement.val at write
  rcases admitted.degree with three | four
  · simp only [factorWords, three, show (3#usize).val + 1 = 4 from rfl] at factorNormal solved
    change bulksketch.decode.deg34.solve fieldDictionary kernels (prefixSlice workspace.polynomials 4)
      (region workspace.polynomials 11 15) = Result.ok (count, replacement) at solved
    simp only [leafOperation, phase, Bool.false_eq_true, ite_false, three, eq_self, ite_true] at chargeNormal
    cases count <;>
      simp [Roots.closed_leaf, stage_test, phase, three, chargeNormal, core.result.Result.Insts.CoreOpsTry.branch,
        split, factorNormal, prefixNormal, factorWords, solved, write, solveFrame, normalReturn] <;> rfl
  · simp only [factorWords, four, show (4#usize).val + 1 = 5 from rfl] at factorNormal solved
    change bulksketch.decode.deg34.solve fieldDictionary kernels (prefixSlice workspace.polynomials 5)
      (region workspace.polynomials 11 15) = Result.ok (count, replacement) at solved
    have different : roots.degree ≠ 3#usize := by rw [four]; decide
    simp only [leafOperation, phase, Bool.false_eq_true, ite_false, different] at chargeNormal
    cases count <;>
      simp [Roots.closed_leaf, stage_test, phase, four, chargeNormal, core.result.Result.Insts.CoreOpsTry.branch,
        split, factorNormal, prefixNormal, factorWords, solved, write, solveFrame, normalReturn] <;> rfl

private theorem certificate_frame (roots : Roots) (workspace : RowWorkspace)
    (degree : roots.degree.val = 3 ∨ roots.degree.val = 4)
    (room : 20 ≤ workspace.polynomials.length) (count : roots.solved_count.val ≤ 4) :
    (certificateResult roots workspace).2.length = 5 ∧
      ((certificateResult roots workspace).1 = true → (candidateWords roots workspace).length = roots.degree.val) := by
  have factorLen := factor_length roots workspace degree (by omega)
  have candidateLen := region_length workspace.polynomials 11 (11 + roots.solved_count.val) (by omega)
  have productLen : (productWords workspace).length = 5 := region_length workspace.polynomials 15 20 room
  unfold certificateResult Certificate.expected
  split
  · rename_i invalid
    constructor
    · exact productLen
    · simp
  · rename_i valid
    have lengths : (candidateWords roots workspace).length + 1 = (factorWords roots workspace).length := by
      by_contra mismatch
      exact valid (Or.inl mismatch)
    simp only [restore_length, productLen, true_and]
    intro _
    omega

private theorem paid_verify {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : Cubic.CorrectArithmetic kernels) (roots : Roots) (stage : Stage)
    (workspace : RowWorkspace) (meter finalMeter : WorkMeter)
    (admitted : Admitted roots stage workspace) (phase : verifying stage = true)
    (chargeNormal : charge meter (leafOperation roots stage) = .ok (.Ok (), finalMeter)) :
    Roots.closed_leaf fieldDictionary kernels roots stage workspace meter =
      verificationFrame roots workspace finalMeter := by
  have room := admitted.verificationRoom phase
  have count := admitted.candidateCount phase
  have degree := degree_values roots admitted.degree
  obtain ⟨productTail, back, split, tailVal, tailLength, join⟩ :=
    split_normal workspace.polynomials 15#usize (by change 15 ≤ workspace.polynomials.length; omega)
  change productTail.length = workspace.polynomials.length - 15 at tailLength
  have prefixNormal := prefix_normal productTail 5#usize (by change 5 ≤ productTail.length; omega)
  change _ = Result.ok (prefixSlice productTail 5, restorePrefix productTail) at prefixNormal
  rw [prefix_tail_region workspace.polynomials productTail 15 5 tailVal] at prefixNormal
  have valuesLength : (prefixSlice workspace.polynomials 15).length = 15 := by
    rw [prefix_length, Nat.min_eq_left (by omega)]
  have factorNormal := inclusive_prefix_normal (prefixSlice workspace.polynomials 15) roots.degree (by omega)
  rw [prefix_prefix _ _ _ (by omega)] at factorNormal
  change core.slice.index.Slice.index (RebuiltLfsrRuntime.inclusive U64) _ ⟨roots.degree⟩ =
    Result.ok (factorWords roots workspace) at factorNormal
  obtain ⟨stop, addCount, stopVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := 11#usize) (y := roots.solved_count)
      (by have maxLen := Slice.length_ineq workspace.polynomials
          change workspace.polynomials.length ≤ Usize.max at maxLen
          change 11 + roots.solved_count.val ≤ Usize.max
          omega))
  change stop.val = 11 + roots.solved_count.val at stopVal
  have candidateNormal := shared_region_normal (prefixSlice workspace.polynomials 15) 11#usize stop
    (by change 11 ≤ stop.val; omega) (by omega)
  change _ = Result.ok (region (prefixSlice workspace.polynomials 15) 11 stop.val) at candidateNormal
  rw [stopVal, region_prefix _ _ _ _ (by omega)] at candidateNormal
  have factorLen := factor_length roots workspace degree (by omega)
  have candidateLen : (candidateWords roots workspace).length = roots.solved_count.val := by
    rw [candidateWords, region_length _ _ _ (by omega)]
    omega
  have productLen : (productWords workspace).length = 5 := region_length _ _ _ room
  have maxLen := Slice.length_ineq workspace.polynomials
  change workspace.polynomials.length ≤ Usize.max at maxLen
  have checked := Certificate.certificate_refines kernels arithmetic.1.1 (factorWords roots workspace)
    (candidateWords roots workspace) (productWords workspace) (by omega) (by intros; omega)
  change _ = Result.ok (certificateResult roots workspace) at checked
  have contract := certificate_frame roots workspace degree room count
  cases certEq : certificateResult roots workspace with
  | mk valid product =>
    rw [certEq] at checked contract
    simp only [factorWords, candidateWords, productWords] at checked
    have joined := join product (by have := contract.1; change product.length = 5 at this; omega)
    change back (prefixSlice workspace.polynomials 15, restorePrefix productTail product) =
      workspace.polynomials.setSlice! 15 product.val at joined
    simp only [leafOperation, phase, ite_true] at chargeNormal
    cases valid with
    | false =>
      simp [Roots.closed_leaf, stage_test, phase, chargeNormal, core.result.Result.Insts.CoreOpsTry.branch,
        split, addCount, candidateNormal, factorNormal, prefixNormal, factorWords,
        checked, joined, verificationFrame, certEq, checkedWorkspace, normalReturn]
      rfl
    | true =>
      have rootRoom := admitted.rootRoom phase (by rw [certEq])
      obtain ⟨nextCount, addRoots, countVal⟩ := RawMulTable.normal_of_spec _ _
        (Usize.add_spec (x := roots.count) (y := roots.degree)
          (by have maxRoots := Slice.length_ineq workspace.roots
              change workspace.roots.length ≤ Usize.max at maxRoots
              omega))
      have dest := mutable_region_normal workspace.roots roots.count nextCount (by omega) (by omega)
      have length : (region workspace.roots roots.count.val nextCount.val).length =
          (candidateWords roots workspace).length := by
        rw [region_length _ _ _ (by omega), contract.2 rfl]
        omega
      have copied := copy_normal _ _ length
      simp only [candidateWords] at copied
      simp [Roots.closed_leaf, stage_test, phase, chargeNormal, core.result.Result.Insts.CoreOpsTry.branch,
        split, addCount, candidateNormal, factorNormal, prefixNormal, factorWords, candidateWords,
        checked, joined, verificationFrame, certEq, checkedWorkspace, acceptedWorkspace, addRoots, dest, copied]

theorem closed_leaf_refines : ActualClosedLeafRefines := by
  intro K kernels roots stage workspace meter arithmetic admitted
  have normal := StageCharge.charge_refines fieldDictionary kernels meter (leafOperation roots stage)
  change charge meter (leafOperation roots stage) = _ at normal
  rw [price_refines roots stage admitted.degree] at normal
  simp only [bind_ok] at normal
  cases charged : StageCharge.chargeResult meter (.Ok (leafPrice roots stage)) with
  | mk result finalMeter =>
    rw [charged] at normal
    cases result with
    | Err error =>
      cases phase : verifying stage with
      | false =>
        by_cases three : roots.degree = 3#usize <;>
          simp [leafOperation, phase, three] at normal <;>
          simp [Roots.closed_leaf, stage_test, phase, three, normal, expected, charged,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from] <;> rfl
      | true =>
        simp [leafOperation, phase] at normal
        simp [Roots.closed_leaf, stage_test, phase, normal, expected, charged,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        rfl
    | Ok empty =>
      cases empty
      cases phase : verifying stage with
      | false =>
        simpa [expected, charged, phase] using paid_solve kernels arithmetic roots stage workspace meter finalMeter
          admitted phase normal
      | true =>
        simpa [expected, charged, phase] using paid_verify kernels arithmetic roots stage workspace meter finalMeter
          admitted phase normal

end BulksketchBridge.ClosedLeaf
