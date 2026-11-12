import BulksketchBridge.DegreeProbeRuntimeRunSpec
import BulksketchBridge.DegreeProbeRuntimeState
import BulksketchBridge.StageCharge
import BulksketchBridge.NewtonGuard
import BulksketchBridge.Normalize
import BulksketchBridge.QuarticSolve
import BulksketchBridge.Certificate

namespace BulksketchBridge.DegreeProbeRuntime

open Aeneas Aeneas.Std Aeneas.Std.WP DenseCoefficient RebuiltLfsr ClosedLeaf
open bulksketch.decode.degree_probe bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.work bulksketch.types bulksketch.backend.contract
open core.result.Result.Insts

set_option maxHeartbeats 2000000

private theorem count_normal (self : DegreeProbe) : DegreeProbe.impl.count self = .ok (countWord self) := rfl

/-- The exact original source price and charge control flow collapses to the meter model. -/
private theorem paid_exact (self : DegreeProbe) (workspace : RowWorkspace) (meter : WorkMeter)
    (operation : Charge) (body : WorkMeter → Result RunResult) :
    (do
      let r ← WorkScheduleV1.cost operation
      let cf ← CoreOpsTry.branch r
      match cf with
      | .Continue cost =>
        let (charge, final) ← WorkMeter.charge meter cost
        let cf1 ← CoreOpsTry.branch charge
        match cf1 with
        | .Continue _ => body final
        | .Break residual =>
          let error ← CoreOpsTry_traitFromResidualResult.from_residual
            (Option Stage) (core.convert.FromSame DecodeError) residual
          .ok (error, self, workspace, id, final)
      | .Break residual =>
        let error ← CoreOpsTry_traitFromResidualResult.from_residual
          (Option Stage) (core.convert.FromSame DecodeError) residual
        .ok (error, self, workspace, id, meter)) = paid self workspace meter operation body := by
  unfold paid
  congr 1
  funext cost
  cases cost with
  | Err error =>
    simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, StageCharge.chargeResult]
  | Ok amount =>
    obtain ⟨final, normal, exact⟩ := BulksketchBridge.WorkMeter.charge_refines meter amount
    have finalEq : final = StageCharge.meterOfModel ((BulksketchBridge.WorkMeter.toModel meter).charge
        (BulksketchBridge.WorkMeter.toUInt64 amount)).1 := by
      apply BulksketchBridge.WorkMeter.toModel_injective
      rw [StageCharge.toModel_meterOfModel]
      exact exact
    simp only [CoreOpsTry.branch, bind_ok, normal, finalEq, StageCharge.chargeResult]
    cases BulksketchBridge.WorkMeter.rustOutcome ((BulksketchBridge.WorkMeter.toModel meter).charge
        (BulksketchBridge.WorkMeter.toUInt64 amount)).2 <;>
      simp [CoreOpsTry_traitFromResidualResult.from_residual]

private theorem paid_body_congr (self : DegreeProbe) (workspace : RowWorkspace) (meter : WorkMeter)
    (operation : Charge) (left right : WorkMeter → Result RunResult)
    (agree : ∀ final, left final = right final) :
    paid self workspace meter operation left = paid self workspace meter operation right := by
  rw [funext agree]

private theorem slice_read (words : Slice U64) (index : Usize) (bound : index.val < words.length) :
    Slice.index_usize words index = .ok words[index.val]! := by
  obtain ⟨word, normal, equal⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words index bound)
  rw [normal, equal, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ bound)

private theorem equality_exact (left right : Slice U64) :
    Aeneas.Std.CertificateRuntime.mutableSharedEq
      (bulksketch.Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU64) left right =
      .ok (decide (left = right)) := by
  change core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU64 left right = _
  obtain ⟨equal, normal, meaning⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU64 left right (by
      intro x y; simp [liftFun2, spec_ok]))
  rw [normal]
  congr 1
  cases equal <;> simp_all

private theorem verified_long {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (encoding : CorrectEncoding kernels) (odd roots scratch : Slice U64)
    (long : 2 < roots.length) (room : odd.length ≤ scratch.length) :
    bulksketch.decode.probe.verified fieldDictionary kernels odd roots scratch =
      .ok (decide (encodedWords (prefixSlice scratch odd.length) roots = odd),
        restorePrefix scratch (encodedWords (prefixSlice scratch odd.length) roots)) := by
  have skip : ¬ roots.len ≤ 2#usize := by scalar_tac
  have window := prefix_normal scratch odd.len (by simpa using room)
  rw [Slice.len_val] at window
  simp only [bulksketch.decode.probe.verified, skip, ite_false, Slice.index_mut_SliceIndexRangeToUsizeSliceInst, window,
    bind_ok]
  dsimp! only
  simp only [encoding (prefixSlice scratch odd.length) roots, equality_exact, bind_ok]

theorem run_canonicalize_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : DegreeProbe) (odd : Slice U64) (budget : RowBudget) (workspace : RowWorkspace) (meter : WorkMeter)
    (admitted : Admitted .canonicalize self odd workspace) :
    DegreeProbe.run fieldDictionary kernels self odd budget workspace meter =
      paid self workspace meter (phasePrice .canonicalize (degreeWord self) odd budget)
        (phaseResult kernels .canonicalize self odd budget workspace) := by
  obtain ⟨_, active, _, room⟩ := admitted
  change self.next = some .Canonicalization at active
  have window := prefix_normal workspace.roots (countWord self) room
  unfold DegreeProbe.run
  simp only [active, core.option.Option.expect, Result.ofOption, bind_ok, lift, count_normal]
  refine (paid_exact self workspace meter _ _).trans ?_
  apply paid_body_congr
  intro final
  simp only [Slice.index_mut_SliceIndexRangeToUsizeSliceInst, window, bind_ok]
  dsimp! only
  simp only [Aeneas.Std.DegreeProbeRuntime.sortUnsigned, bind_ok]
  rfl

theorem run_verify_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : DegreeProbe) (odd : Slice U64) (budget : RowBudget) (workspace : RowWorkspace) (meter : WorkMeter)
    (encoding : CorrectEncoding kernels) (admitted : Admitted .verify self odd workspace) :
    DegreeProbe.run fieldDictionary kernels self odd budget workspace meter =
      paid self workspace meter (phasePrice .verify (degreeWord self) odd budget)
        (phaseResult kernels .verify self odd budget workspace) := by
  obtain ⟨degrees, active, countEq, rootsRoom, verifyRoom⟩ := admitted
  change self.next = some .Verification at active
  have window := shared_prefix_normal workspace.roots (countWord self) rootsRoom
  have length : (prefixSlice workspace.roots (countWord self).val).length = (countWord self).val := by
    rw [prefix_length, Nat.min_eq_left rootsRoom]
  have lower : 2 < (degreeWord self).val := by rcases degrees with equal | equal <;> simp [equal]
  have verified := verified_long kernels encoding odd (prefixSlice workspace.roots (countWord self).val)
    workspace.verification (by rw [length, countEq]; exact lower) verifyRoom
  unfold DegreeProbe.run
  simp only [active, core.option.Option.expect, Result.ofOption, bind_ok, lift, count_normal]
  refine (paid_exact self workspace meter _ _).trans ?_
  apply paid_body_congr
  intro final
  simp only [Slice.index_SliceIndexRangeToUsizeSliceInst, window, verified, bind_ok]
  dsimp! only
  have countValue : (countWord self).val = self.count.val := U8.cast_Usize_val_eq _
  by_cases accepted : encodedWords (prefixSlice workspace.verification odd.length)
      (prefixSlice workspace.roots self.count.val) = odd <;>
    simp [accepted, countValue, phaseResult, resultOfState, reject_refines self odd.len budget, bind_ok] <;> rfl

theorem run_guard_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : DegreeProbe) (odd : Slice U64) (budget : RowBudget) (workspace : RowWorkspace) (meter : WorkMeter)
    (arithmetic : Cubic.CorrectArithmetic kernels) (admitted : Admitted .guard self odd workspace) :
    DegreeProbe.run fieldDictionary kernels self odd budget workspace meter =
      paid self workspace meter (phasePrice .guard (degreeWord self) odd budget)
        (phaseResult kernels .guard self odd budget workspace) := by
  obtain ⟨degrees, active, oddRoom, polyRoom⟩ := admitted
  let window := region workspace.polynomials 5 11
  have windowRoom : window.length = 6 := region_length _ _ _ polyRoom
  have take : core.slice.index.SliceIndexRangeUsizeSlice.index_mut ⟨5#usize, 11#usize⟩ workspace.polynomials =
      .ok (window, fun replacement => workspace.polynomials.setSlice! 5 replacement.val) :=
    mutable_region_normal _ _ _ (by decide) polyRoom
  have guardNormal := NewtonGuard.guard_refines kernels odd (degreeWord self) window
    ⟨arithmetic.1.1, arithmetic.1.2.1⟩ ⟨degrees, oddRoom, fun _ => by omega⟩
  -- Introduce the exact pair before reducing the branch of the original body.
  have four_ne_three : (4#usize : Usize) ≠ 3#usize := by decide
  rcases degrees with degree | degree
  all_goals
    simp only [phaseStage, degree, four_ne_three, ite_true, ite_false] at active
    unfold DegreeProbe.run
    simp only [active, core.option.Option.expect, Result.ofOption, bind_ok, lift, count_normal,
      phasePrice, degree, four_ne_three, ite_true, ite_false]
    refine (paid_exact self workspace meter _ _).trans ?_
    apply paid_body_congr
    intro final
    have exactGuard : bulksketch.decode.deg34.guard fieldDictionary kernels odd (degreeWord self) window =
        .ok (NewtonGuard.expected odd (degreeWord self) window) := guardNormal
    rw [degree] at exactGuard
    cases decision : NewtonGuard.expected odd (degreeWord self) window with
    | mk ok output =>
      rw [degree] at decision
      rw [decision] at exactGuard
      cases ok <;> simp [Slice.index_mut_SliceIndexRangeUsizeSliceInst, take, exactGuard,
        phaseResult, phaseStage, degree, resultOfState, reject_refines self odd.len budget, decision, window, bind_ok] <;> rfl

private theorem split_head (words : Slice U64) (stop : Usize) (room : stop.val ≤ words.length) :
    ∃ tail back,
      core.slice.Slice.split_at_mut words stop = .ok ((prefixSlice words stop.val, tail), back) ∧
      tail.val = words.val.drop stop.val ∧ tail.length = words.length - stop.val ∧
      ∀ head : Slice U64, head.length = stop.val → back (head, tail) = restorePrefix words head := by
  obtain ⟨⟨⟨head, tail⟩, back⟩, normal, headLen, tailLen, headVal, tailVal, backValues⟩ :=
    RawMulTable.normal_of_spec _ _ (core.slice.Slice.split_at_mut.spec words stop room)
  have headEq : head = prefixSlice words stop.val := Slice.ext _ _ (by simpa only [prefixSlice, Slice.from_val] using headVal)
  subst head
  refine ⟨tail, back, normal, tailVal, tailLen, ?_⟩
  intro head h
  apply Slice.ext
  rw [(backValues head tail h tailLen).1]
  simp only [restorePrefix, Slice.from_val, List.setSlice!, List.take_zero, List.nil_append, Nat.sub_zero, Nat.zero_add,
    Nat.min_eq_left (show stop.val ≤ words.val.length from room), tailVal, show head.val.length = stop.val from h]
  have take : head.val.take stop.val = head.val := by rw [← h, List.take_length]
  rw [take]

theorem run_normalize_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : DegreeProbe) (odd : Slice U64) (budget : RowBudget) (workspace : RowWorkspace) (meter : WorkMeter)
    (arithmetic : Cubic.CorrectArithmetic kernels) (admitted : Admitted .normalize self odd workspace) :
    DegreeProbe.run fieldDictionary kernels self odd budget workspace meter =
      paid self workspace meter (phasePrice .normalize (degreeWord self) odd budget)
        (phaseResult kernels .normalize self odd budget workspace) := by
  obtain ⟨degrees, active, oddRoom, polyRoom, denominatorNZ⟩ := admitted
  let poly := workspace.polynomials
  obtain ⟨tail, back, split, tailVal, tailLen, writeBack⟩ := split_head poly 5#usize (by change 5 ≤ workspace.polynomials.length; omega)
  have window : core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨6#usize⟩ tail =
      .ok (region poly 5 11) := by
    have normal := shared_prefix_normal tail 6#usize (by
      rw [tailLen]; change 6 ≤ workspace.polynomials.length - 5; omega)
    change _ = Result.ok (prefixSlice tail 6) at normal
    rw [prefix_tail_region poly tail 5 6 tailVal] at normal
    exact normal
  have read : Slice.index_usize odd 0#usize = .ok odd[0]! := slice_read odd 0#usize oddRoom
  have degreeNat : (degreeWord self).val = 3 ∨ (degreeWord self).val = 4 := by
    rcases degrees with equal | equal <;> simp [equal]
  have norm := Normalize.normalize_refines kernels ⟨arithmetic.1.1, arithmetic.2.1⟩ (region poly 5 11)
    odd[0]! (degreeWord self) (prefixSlice poly 5) degreeNat
    (by rw [region_length _ _ _ polyRoom])
    (by rw [prefix_length, Nat.min_eq_left (by change 5 ≤ workspace.polynomials.length; omega)]; omega)
    denominatorNZ
  let expected := Normalize.expectedOutput (region poly 5 11) odd[0]! (degreeWord self).val (prefixSlice poly 5)
  have restore : back (expected, tail) = restorePrefix poly expected := by
    apply writeBack
    rw [show expected.length = (prefixSlice poly 5).length from Normalize.expected_length _ _ _ _,
      prefix_length, Nat.min_eq_left (by change 5 ≤ workspace.polynomials.length; omega)]
    rfl
  have four_ne_three : (4#usize : Usize) ≠ 3#usize := by decide
  rcases degrees with degree | degree
  all_goals
    simp only [phaseStage, degree, four_ne_three, ite_true, ite_false] at active
    unfold DegreeProbe.run
    simp only [active, core.option.Option.expect, Result.ofOption, bind_ok, lift, count_normal,
      phasePrice, degree, four_ne_three, ite_true, ite_false]
    refine (paid_exact self workspace meter _ _).trans ?_
    apply paid_body_congr
    intro final
    have exactNorm : bulksketch.decode.deg34.normalize fieldDictionary kernels (region poly 5 11)
        odd[0]! (degreeWord self) (prefixSlice poly 5) = .ok expected := norm
    simp [degree, poly] at exactNorm restore
    simp [split, window, Slice.index_SliceIndexRangeToUsizeSliceInst, read, exactNorm, bind_ok,
      restore, phaseResult, phaseStage, degree, four_ne_three, resultOfState, poly]
    simp [expected, degree, poly]
  all_goals rfl

private theorem solver_exact {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : Cubic.CorrectArithmetic kernels) (degree : Usize) (poly : Slice U64)
    (admitted : degree = 3#usize ∨ degree = 4#usize) (room : 15 ≤ poly.length) :
    ∃ result : Option Usize × Slice U64,
      bulksketch.decode.deg34.solve fieldDictionary kernels (prefixSlice poly (degree.val + 1))
        (region poly 11 15) = .ok result ∧
      result.2.length = 4 ∧ (result.1 = none ∨ result.1 = some degree) := by
  have degreeNat : degree.val = 3 ∨ degree.val = 4 := by rcases admitted with equal | equal <;> simp [equal]
  have factorLen : (prefixSlice poly (degree.val + 1)).length = degree.val + 1 := by
    rw [prefix_length, Nat.min_eq_left (by omega)]
  have outputLen : (region poly 11 15).length = 4 := region_length _ _ _ room
  obtain ⟨result, normal, cubic, quartic⟩ := QuarticSolve.solve_refines kernels (prefixSlice poly (degree.val + 1))
    (region poly 11 15) arithmetic (by omega) (by omega)
  refine ⟨result, normal, ?_⟩
  rcases admitted with three | four
  · obtain ⟨candidates, _, frame⟩ := cubic (by rw [factorLen, three]; rfl)
    rw [frame]
    cases candidates <;> simp [QuarticSolve.expectedFrame, outputLen, three]
  · obtain ⟨candidates, _, frame⟩ := quartic (by rw [factorLen, four]; rfl)
    rw [frame]
    cases candidates <;> simp [QuarticSolve.expectedFrame, outputLen, four]

theorem run_leaf_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : DegreeProbe) (odd : Slice U64) (budget : RowBudget) (workspace : RowWorkspace) (meter : WorkMeter)
    (arithmetic : Cubic.CorrectArithmetic kernels) (admitted : Admitted .leaf self odd workspace) :
    DegreeProbe.run fieldDictionary kernels self odd budget workspace meter =
      paid self workspace meter (phasePrice .leaf (degreeWord self) odd budget)
        (phaseResult kernels .leaf self odd budget workspace) := by
  obtain ⟨degrees, active, room⟩ := admitted
  change 15 ≤ workspace.polynomials.length at room
  have dNat : (degreeWord self).val = 3 ∨ (degreeWord self).val = 4 := by
    rcases degrees with equal | equal <;> simp [equal]
  obtain ⟨rest, back, split, restVal, restLen, join⟩ :=
    split_normal workspace.polynomials 11#usize (by change 11 ≤ workspace.polynomials.length; omega)
  change rest.length = workspace.polynomials.length - 11 at restLen
  have prefixLen : (prefixSlice workspace.polynomials 11).length = 11 := by
    rw [prefix_length, Nat.min_eq_left (by omega)]
  have factorNormal := inclusive_prefix_normal (prefixSlice workspace.polynomials 11) (degreeWord self) (by omega)
  rw [prefix_prefix _ _ _ (by omega)] at factorNormal
  change core.slice.index.Slice.index (Aeneas.Std.RebuiltLfsrRuntime.inclusive U64) _ ⟨degreeWord self⟩ =
    Result.ok (prefixSlice workspace.polynomials ((degreeWord self).val + 1)) at factorNormal
  have candidateNormal := prefix_normal rest 4#usize (by change 4 ≤ rest.length; omega)
  change _ = Result.ok (prefixSlice rest 4, restorePrefix rest) at candidateNormal
  rw [prefix_tail_region workspace.polynomials rest 11 4 restVal] at candidateNormal
  obtain ⟨⟨outcome, replacement⟩, solved, replacementLen, outcomeShape⟩ :=
    solver_exact kernels arithmetic (degreeWord self) workspace.polynomials degrees room
  change replacement.length = 4 at replacementLen
  have restored := join replacement (by omega)
  change back (prefixSlice workspace.polynomials 11, restorePrefix rest replacement) =
    workspace.polynomials.setSlice! 11 replacement.val at restored
  have conversion : Aeneas.Std.DegreeProbeRuntime.usizeToU8 (degreeWord self) =
      Result.ok (.Ok (UScalar.cast .U8 (degreeWord self))) := by
    have fits : (degreeWord self).val ≤ UScalar.max .U8 := by scalar_tac
    simp only [Aeneas.Std.DegreeProbeRuntime.usizeToU8, core.num.tryFromUScalar, fits, ite_true]
  have four_ne_three : (4#usize : Usize) ≠ 3#usize := by decide
  rcases degrees with degree | degree
  all_goals
    simp only [phaseStage, degree, four_ne_three, ite_true, ite_false] at active
    unfold DegreeProbe.run
    simp only [active, core.option.Option.expect, Result.ofOption, bind_ok, lift, count_normal,
      phasePrice, degree, four_ne_three, ite_true, ite_false]
    refine (paid_exact self workspace meter _ _).trans ?_
    apply paid_body_congr
    intro final
    simp [degree] at factorNormal solved conversion
    rcases outcomeShape with miss | hit
    · change outcome = none at miss
      subst outcome
      simp [split, factorNormal, candidateNormal, solved, restored, phaseResult, degree, reject_refines self odd.len budget,
        resultOfState, bind_ok]
      rfl
    · change outcome = some (degreeWord self) at hit
      subst outcome
      simp [split, factorNormal, candidateNormal, solved, restored, phaseResult, degree, conversion,
        core.result.Result.expect, resultOfState, bind_ok]
      rfl

theorem run_certificate_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : DegreeProbe) (odd : Slice U64) (budget : RowBudget) (workspace : RowWorkspace) (meter : WorkMeter)
    (arithmetic : Cubic.CorrectArithmetic kernels) (admitted : Admitted .certificate self odd workspace) :
    DegreeProbe.run fieldDictionary kernels self odd budget workspace meter =
      paid self workspace meter (phasePrice .certificate (degreeWord self) odd budget)
        (phaseResult kernels .certificate self odd budget workspace) := by
  obtain ⟨degrees, active, countEq, room, rootsRoom⟩ := admitted
  change self.next = some .FactorVerification at active
  have dNat : (degreeWord self).val = 3 ∨ (degreeWord self).val = 4 := by
    rcases degrees with equal | equal <;> simp [equal]
  let poly := workspace.polynomials
  let factor := prefixSlice poly ((degreeWord self).val + 1)
  let roots := region poly 11 (11 + (countWord self).val)
  let product := region poly 15 20
  obtain ⟨tail, back, split, tailVal, tailLen, join⟩ :=
    split_normal poly 15#usize (by change 15 ≤ workspace.polynomials.length; omega)
  change tail.length = workspace.polynomials.length - 15 at tailLen
  have productNormal := prefix_normal tail 5#usize (by change 5 ≤ tail.length; omega)
  change _ = Result.ok (prefixSlice tail 5, restorePrefix tail) at productNormal
  rw [prefix_tail_region poly tail 15 5 tailVal] at productNormal
  have prefixLen : (prefixSlice poly 15).length = 15 := by
    rw [prefix_length, Nat.min_eq_left (by change 15 ≤ workspace.polynomials.length; omega)]
  have factorNormal := inclusive_prefix_normal (prefixSlice poly 15) (degreeWord self) (by omega)
  rw [prefix_prefix _ _ _ (by omega)] at factorNormal
  change core.slice.index.Slice.index (Aeneas.Std.RebuiltLfsrRuntime.inclusive U64) _ ⟨degreeWord self⟩ =
    Result.ok factor at factorNormal
  have maxLen := Slice.length_ineq workspace.polynomials
  change workspace.polynomials.length ≤ Usize.max at maxLen
  obtain ⟨stop, addCount, stopVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := 11#usize) (y := countWord self) (by
      change 11 + (countWord self).val ≤ Usize.max; omega))
  change stop.val = 11 + (countWord self).val at stopVal
  have candidates := shared_region_normal (prefixSlice poly 15) 11#usize stop
    (by change 11 ≤ stop.val; omega) (by omega)
  change _ = Result.ok (region (prefixSlice poly 15) 11 stop.val) at candidates
  rw [stopVal, region_prefix _ _ _ _ (by omega)] at candidates
  have factorLen : factor.length = (degreeWord self).val + 1 := by
    change (prefixSlice poly ((degreeWord self).val + 1)).length = _
    have fits : (degreeWord self).val + 1 ≤ poly.length := by change (degreeWord self).val + 1 ≤ workspace.polynomials.length; omega
    rw [prefix_length, Nat.min_eq_left fits]
  have rootsLen : roots.length = (countWord self).val := by
    change (region poly 11 (11 + (countWord self).val)).length = _
    rw [region_length _ _ _ (by change 11 + (countWord self).val ≤ workspace.polynomials.length; omega)]
    omega
  have productLen : product.length = 5 := region_length _ _ _ room
  have certificate := Certificate.certificate_refines kernels arithmetic.1.1 factor roots product (by omega) (by intros; omega)
  have resultLen : (Certificate.expected factor roots product).2.length = 5 := by
    unfold Certificate.expected
    split <;> simp [productLen]
  have rootOutput := prefix_normal workspace.roots (countWord self) rootsRoom
  have copied : core.slice.Slice.copy_from_slice core.marker.CopyU64
      (prefixSlice workspace.roots (countWord self).val) roots = Result.ok roots := by
    apply copy_normal
    rw [prefix_length, Nat.min_eq_left rootsRoom, rootsLen]
  cases cert : Certificate.expected factor roots product with
  | mk accepted words =>
    rw [cert] at certificate resultLen
    change words.length = 5 at resultLen
    have restored := join words (by omega)
    change back (prefixSlice poly 15, restorePrefix tail words) = poly.setSlice! 15 words.val at restored
    unfold DegreeProbe.run
    simp only [active, core.option.Option.expect, Result.ofOption, bind_ok, lift, count_normal]
    refine (paid_exact self workspace meter _ _).trans ?_
    apply paid_body_congr
    intro final
    simp [factor, roots, product, poly] at certificate cert copied restored
    cases accepted <;>
      simp [split, factorNormal, addCount, candidates, productNormal, rootOutput, copied, restored,
        certificate, phaseResult, resultOfState, reject_refines self odd.len budget, cert, factor, poly,
        bind_ok, Slice.index_SliceIndexRangeUsizeSliceInst, Slice.index_mut_SliceIndexRangeToUsizeSliceInst] <;> rfl

theorem run_refines : ActualDegreeProbeRun := by
  intro K kernels phase self odd budget workspace meter arithmetic encoding admitted
  cases phase with
  | guard => exact run_guard_refines kernels self odd budget workspace meter arithmetic admitted
  | normalize => exact run_normalize_refines kernels self odd budget workspace meter arithmetic admitted
  | leaf => exact run_leaf_refines kernels self odd budget workspace meter arithmetic admitted
  | certificate => exact run_certificate_refines kernels self odd budget workspace meter arithmetic admitted
  | verify => exact run_verify_refines kernels self odd budget workspace meter (encoding rfl) admitted
  | canonicalize => exact run_canonicalize_refines kernels self odd budget workspace meter admitted

end BulksketchBridge.DegreeProbeRuntime
