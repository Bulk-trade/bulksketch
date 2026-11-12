import Arithmetic.TinyProbeGenerated
import BulksketchBridge.StageCharge
import BulksketchBridge.RowDispatch

namespace BulksketchBridge.TinyProbe

open Aeneas Aeneas.Std Result
open bulksketch.decode.probe bulksketch.decode.row bulksketch.decode.work bulksketch.types
open bulksketch.backend.contract
open core.result.Result.Insts

set_option maxRecDepth 4096
set_option maxHeartbeats 700000

def operation (self : Probe) (capacity : Usize) : Option Charge :=
  match self.next with
  | some .DirectOne => some .DirectOne
  | some .DirectTwo => some .DirectTwo
  | some .Verification => some (.Verify capacity self.budget.total)
  | some .Canonicalization => some (.Canonicalize self.budget.total)
  | _ => none

def paid (op : Charge) (meter : WorkMeter) : Result (core.result.Result Unit DecodeError × WorkMeter) := do
  let cost ← WorkScheduleV1.cost op
  .ok (StageCharge.chargeResult meter cost)

def chargeExpected (self : Probe) (capacity : Usize) (meter : WorkMeter) :
    Result (core.result.Result Unit DecodeError × WorkMeter) :=
  match operation self capacity with
  | none => .fail .panic
  | some op => paid op meter

private theorem charge_control (op : Charge) (meter : WorkMeter) :
    (do
      let r ← WorkScheduleV1.cost op
      let cf ← CoreOpsTry.branch r
      match cf with
      | .Continue val =>
        let (r1, meter1) ← WorkMeter.charge meter val
        let cf1 ← CoreOpsTry.branch r1
        match cf1 with
        | .Continue _ => ok (core.result.Result.Ok (), meter1)
        | .Break residual =>
          let r2 ← CoreOpsTry_traitFromResidualResult.from_residual Unit
            (core.convert.FromSame DecodeError) residual
          ok (r2, meter1)
      | .Break residual =>
        let r1 ← CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame DecodeError) residual
        ok (r1, meter)) = paid op meter := by
  unfold paid
  congr 1
  funext cost
  cases cost with
  | Err error =>
    simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, StageCharge.chargeResult]
  | Ok amount =>
    simp only [CoreOpsTry.branch, bind_ok, StageCharge.meter_charge_refines]
    dsimp! only
    cases charged : BulksketchBridge.WorkMeter.rustOutcome
        ((BulksketchBridge.WorkMeter.toModel meter).charge (BulksketchBridge.WorkMeter.toUInt64 amount)).2 <;>
      simp [CoreOpsTry_traitFromResidualResult.from_residual]

def ActualTinyProbeCharge : Prop :=
  ∀ (self : Probe) (capacity : Usize) (meter : WorkMeter),
    Probe.charge self capacity meter = chargeExpected self capacity meter

theorem tiny_probe_charge : ActualTinyProbeCharge := by
  intro self capacity meter
  cases active : self.next with
  | none => simp [Probe.charge, chargeExpected, operation, active, core.option.Option.expect]
  | some stage =>
    cases stage <;> simp only [Probe.charge, chargeExpected, operation, active,
      core.option.Option.expect, ofOption, bind_ok, bind_fail] <;> try exact charge_control _ _

abbrev Frame := core.result.Result RowProgress DecodeError × Probe × Slice U64 × Slice U64 × WorkMeter

def runExpected {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (self : Probe) (difference verification roots : Slice U64) (meter : WorkMeter) : Result Frame := do
  let (status, after) ← chargeExpected self difference.len meter
  match status with
  | .Err error => .ok (.Err error, self, verification, roots, after)
  | .Ok _ =>
    let (progress, self', verification', roots') ← Probe.run_charged field kernels self difference verification roots
    .ok (.Ok progress, self', verification', roots', after)

def ActualTinyProbeRunNext : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (self : Probe) (difference verification roots : Slice U64) (meter : WorkMeter),
    Probe.run_next field kernels self difference verification roots meter =
      runExpected field kernels self difference verification roots meter

theorem tiny_probe_run_next : ActualTinyProbeRunNext := by
  intro F K field kernels self difference verification roots meter
  unfold Probe.run_next runExpected
  dsimp only
  rw [tiny_probe_charge self difference.len meter]
  congr 1
  funext paid
  rcases paid with ⟨status, after⟩
  cases status <;>
    simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]

def dispatchExpected {F : Type} (d : RowDispatchRuntime.Dictionaries) (field : bulksketch.field.BinaryField F)
    (backend : BackendId) (self : Probe) (difference verification roots : Slice U64) (meter : WorkMeter) : Result Frame :=
  match backend with
  | .Portable => runExpected field (d.portable field) self difference verification roots meter
  | .Pclmul => runExpected field (d.pclmul field) self difference verification roots meter
  | .Vpclmul512 => runExpected field (d.vpclmul512 field) self difference verification roots meter
  | .Vpclmul256 => .fail .panic

def ActualRunProbeDispatch : Prop :=
  ∀ (d : RowDispatchRuntime.Dictionaries) {F : Type} (field : bulksketch.field.BinaryField F)
    (backend : BackendId) (self : Probe) (difference verification roots : Slice U64) (meter : WorkMeter),
    bulksketch.sketch.dispatch.run_probe d field backend self difference verification roots meter =
      dispatchExpected d field backend self difference verification roots meter

theorem run_probe_dispatch : ActualRunProbeDispatch := by
  intro d F field backend self difference verification roots meter
  cases backend <;> simp only [bulksketch.sketch.dispatch.run_probe, dispatchExpected] <;>
    exact tiny_probe_run_next field _ self difference verification roots meter

#print axioms tiny_probe_charge
#print axioms tiny_probe_run_next
#print axioms run_probe_dispatch

end BulksketchBridge.TinyProbe
