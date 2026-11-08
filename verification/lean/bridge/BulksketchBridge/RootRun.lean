import BulksketchBridge.RootRunSpec
import BulksketchBridge.RootRunPrice

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open core.result.Result.Insts

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem made_buffers (roots : Roots) (workspace : RowWorkspace) (ready : factorReady roots workspace) :
    FactorWork.new roots.degree workspace.polynomials workspace.square_table workspace.raw workspace.basis =
      .ok (buffersFor roots workspace, RootSetup.restoreWork roots.degree.val workspace.polynomials workspace.square_table) :=
  RootSetup.factor_work_refines roots.degree workspace.polynomials workspace.square_table workspace.raw workspace.basis
    ready.1 ready.2

private theorem small_usize : 4160 ≤ Usize.max := by
  simp only [Usize.max, Usize.numBits, UScalarTy.numBits]
  rcases System.Platform.numBits_eq with width | width <;> rw [width] <;> decide

theorem subspace_start_refines : ActualSubspaceStart := by
  intro rank rankBound
  have product : rank.val * (rank.val + 1) ≤ Usize.max := by
    exact (Nat.mul_le_mul rankBound (by omega : rank.val + 1 ≤ 65)).trans small_usize
  obtain ⟨next, addOk, nextVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := rank) (y := 1#usize) (by have := small_usize; change rank.val + 1 ≤ Usize.max; omega))
  change next.val = rank.val + 1 at nextVal
  obtain ⟨mul, mulOk, mulVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := rank) (y := next) (by rw [nextVal]; exact product))
  obtain ⟨offset, divOk, divVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.div_spec mul (y := 2#usize) (by simp))
  refine ⟨offset, ?_, ?_⟩
  · simp only [bulksketch.decode.affine.subspace_start, addOk, mulOk, divOk, bind_ok]
  · change offset.val = mul.val / 2 at divVal
    rw [divVal, mulVal, nextVal]
    rfl

private theorem reducer_stage (calls : Calls) (division : DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64) (roots : Roots) (workspace : RowWorkspace)
    (meter : WorkMeter) (ready : factorReady roots workspace) :
    Roots.run calls division dictionary kernels roots .ReducerPreparation workspace meter =
      reducer kernels roots workspace meter := by
  have made := made_buffers roots workspace ready
  have charged := roots_charge_returns meter (.Table roots.degree) (tableCost roots.degree) (table_cost_refines _)
  simp [Roots.run, Stage.Insts.CoreCmpPartialEqStage.eq, Stage.read_discriminant, made]
  cases paid : StageCharge.chargeResult meter (tableCost roots.degree) with
  | mk reply final =>
    rw [paid] at charged
    cases reply with
    | Err reason =>
      simp only [reducer, charged, bind_ok, CoreOpsTry.branch]
      dsimp! only
      simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from, frame, rebuild]
      simp only [Bind.bind, bind_ok]
      rfl
    | Ok unit =>
      cases unit
      simp only [reducer, charged, bind_ok, CoreOpsTry.branch]
      dsimp! only
      cases affine : roots.affine <;> cases ready : roots.affine_ready <;>
        simp only [tableStage, affine, ready, Bool.false_eq_true, ite_false, ite_true, frame, rebuild, bind_ok] <;> rfl

private theorem trace_stage (calls : Calls) (division : DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64) (roots : Roots) (workspace : RowWorkspace)
    (meter : WorkMeter) (ready : factorReady roots workspace) :
    Roots.run calls division dictionary kernels roots .Trace workspace meter =
      expected calls division kernels roots .Trace workspace meter := by
  have made := made_buffers roots workspace ready
  simp [Roots.run, Stage.Insts.CoreCmpPartialEqStage.eq, Stage.read_discriminant, made]
  rfl

private theorem divide_stage (calls : Calls) (division : DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64) (roots : Roots) (workspace : RowWorkspace)
    (meter : WorkMeter) (ready : factorReady roots workspace) :
    Roots.run calls division dictionary kernels roots .FactorDivision workspace meter =
      expected calls division kernels roots .FactorDivision workspace meter := by
  have made := made_buffers roots workspace ready
  simp [Roots.run, Stage.Insts.CoreCmpPartialEqStage.eq, Stage.read_discriminant, made]
  rfl

private theorem gcd_stage (calls : Calls) (division : DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64) (roots : Roots) (workspace : RowWorkspace)
    (meter : WorkMeter) (ready : Ready division kernels roots .Gcd workspace meter) :
    Roots.run calls division dictionary kernels roots .Gcd workspace meter =
      gcdStage division kernels roots workspace meter := by
  obtain ⟨⟨polyRoom, tableRoom⟩, paidReady⟩ := ready
  have charged := roots_charge_returns meter (.Gcd roots.degree) (gcdCost roots.degree) (gcd_cost_refines _)
  cases paid : StageCharge.chargeResult meter (gcdCost roots.degree) with
  | mk reply final =>
    rw [paid] at charged
    cases reply with
    | Err reason =>
      rw [run_gcd_charge_failure calls division kernels roots workspace meter final reason polyRoom tableRoom charged]
      simp only [gcdStage, charged, bind_ok, frame]
      rfl
    | Ok unit =>
      cases unit
      obtain ⟨traceRoom, size, gcd, work, raw, exactCall, admitted⟩ := paidReady final charged
      rw [run_gcd_paid calls division kernels roots workspace meter final polyRoom tableRoom traceRoom charged
        size gcd work raw exactCall admitted]
      simp only [gcdStage, charged, bind_ok, exactCall, frame]
      rfl

private theorem affine_stage (calls : Calls) (division : DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64) (roots : Roots) (workspace : RowWorkspace)
    (meter : WorkMeter) (ready : Ready division kernels roots .AffineSplit workspace meter) :
    Roots.run calls division dictionary kernels roots .AffineSplit workspace meter =
      affineSplit calls kernels roots workspace meter := by
  obtain ⟨factor, paidReady⟩ := ready
  have made := made_buffers roots workspace factor
  have charged := roots_charge_returns meter (.AffineSplit roots.degree roots.affine_rank)
    (affineSplitCost roots.degree roots.affine_rank) (affine_split_cost_refines _ _)
  simp [Roots.run, Stage.Insts.CoreCmpPartialEqStage.eq, Stage.read_discriminant, made]
  cases paid : StageCharge.chargeResult meter (affineSplitCost roots.degree roots.affine_rank) with
  | mk reply final =>
    rw [paid] at charged
    cases reply with
    | Err reason =>
      simp only [affineSplit, charged, bind_ok, CoreOpsTry.branch]
      dsimp! only
      simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from, frame, rebuild]
      simp only [Bind.bind, bind_ok]
      rfl
    | Ok unit =>
      cases unit
      simp only [affineSplit, charged, bind_ok, CoreOpsTry.branch]
      dsimp! only
      by_cases zero : roots.affine_rank = 0#usize
      · simp only [zero, ite_true, frame, rebuild, bind_ok, Bind.bind]
        rfl
      · obtain ⟨rankMax, window⟩ := paidReady final charged zero
        have rankPositive : 1 ≤ roots.affine_rank.val := by
          by_contra notPositive
          apply zero
          apply UScalar.eq_of_val_eq
          change roots.affine_rank.val = 0
          omega
        obtain ⟨rank, subOk, rankVal, _⟩ := RawMulTable.normal_of_spec _ _
          (Usize.sub_spec (x := roots.affine_rank) (y := 1#usize) (by exact rankPositive))
        change rank.val = roots.affine_rank.val - 1 at rankVal
        obtain ⟨offset, offsetOk, offsetVal⟩ := subspace_start_refines rank (by omega)
        have factorsMax : workspace.factors.length ≤ Usize.max := workspace.factors.length_ineq
        have strideFits : roots.stride.val * roots.stride.val ≤ Usize.max := by
          unfold affineStop affineStart at window
          omega
        obtain ⟨base, mulOk, baseVal⟩ := RawMulTable.normal_of_spec _ _
          (Usize.mul_spec (x := roots.stride) (y := roots.stride) strideFits)
        have startFits : base.val + offset.val ≤ Usize.max := by
          unfold affineStop affineStart at window
          rw [baseVal, offsetVal, rankVal]
          omega
        obtain ⟨start, startOk, startVal⟩ := RawMulTable.normal_of_spec _ _
          (Usize.add_spec (x := base) (y := offset) startFits)
        have exactStart : start.val = affineStart roots := by
          rw [startVal, baseVal, offsetVal, rankVal, affineStart]
        have limitFits : start.val + rank.val ≤ Usize.max := by
          rw [exactStart, rankVal]
          unfold affineStop at window
          omega
        obtain ⟨limit, limitOk, limitVal⟩ := RawMulTable.normal_of_spec _ _
          (Usize.add_spec (x := start) (y := rank) limitFits)
        obtain ⟨stop, stopOk, stopVal⟩ := RawMulTable.normal_of_spec _ _
          (Usize.add_spec (x := limit) (y := 1#usize) (by
            change limit.val + 1 ≤ Usize.max
            rw [limitVal, exactStart, rankVal]
            unfold affineStop at window
            omega))
        have exactStop : stop.val = affineStop roots := by
          change stop.val = limit.val + 1 at stopVal
          rw [stopVal, limitVal, exactStart, rankVal, affineStop]
          omega
        have region := ClosedLeaf.shared_region_normal workspace.factors start stop (by omega) (by omega)
        simp only [zero, ite_false, subOk, mulOk, offsetOk, startOk, limitOk, stopOk, bind_ok,
          core.slice.index.Slice.index, region, exactStart, exactStop, frame, rebuild]
        rfl

theorem run_refines : ActualRootRun := by
  intro calls division K kernels roots stage workspace meter ready
  cases stage
  case ReducerPreparation =>
    exact reducer_stage calls division kernels roots workspace meter ready
  case AffineSplit =>
    exact affine_stage calls division kernels roots workspace meter ready
  case Gcd =>
    exact gcd_stage calls division kernels roots workspace meter ready
  case Trace =>
    exact trace_stage calls division kernels roots workspace meter ready
  case FactorDivision =>
    exact divide_stage calls division kernels roots workspace meter ready
  all_goals
    first
    | (have made := made_buffers roots workspace ready
       simp [Roots.run, expected, Stage.Insts.CoreCmpPartialEqStage.eq, Stage.read_discriminant, made])
    | simp [Roots.run, expected, Stage.Insts.CoreCmpPartialEqStage.eq, Stage.read_discriminant]

end BulksketchBridge.RootRun
