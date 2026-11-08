import BulksketchBridge.StageChargeSpec
import BulksketchBridge.WorkSchedule
import BulksketchBridge.WorkMeter

namespace BulksketchBridge.StageCharge

open Aeneas Aeneas.Std

@[simp] theorem toModel_meterOfModel (meter : WorkMeter.ModelMeter) :
    WorkMeter.toModel (meterOfModel meter) = meter := by
  cases meter
  simp only [meterOfModel, WorkMeter.toModel, WorkMeter.toUInt64]

/-- The exact source wrapper either propagates the pricing error with the
input meter or executes the already verified WorkMeter charge. -/
theorem charge_refines : ChargeRefines := by
  intro F K field kernels meter operation
  unfold bulksketch.decode.stages.Execution.charge
  congr 1
  funext cost
  cases cost with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, chargeResult]
  | Ok amount =>
    obtain ⟨final, charged, state⟩ := WorkMeter.charge_refines meter amount
    have exactState : final = meterOfModel ((WorkMeter.toModel meter).charge (WorkMeter.toUInt64 amount)).1 := by
      apply WorkMeter.toModel_injective
      rw [toModel_meterOfModel]
      exact state
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, chargeResult]
    rw [charged, exactState]

theorem charge_refines_with_cost {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : bulksketch.backend.contract.BulkKernels K F)
    (meter : bulksketch.types.WorkMeter) (operation : bulksketch.decode.work.Charge)
    (cost : WorkSchedule.CostResult)
    (priced : bulksketch.decode.work.WorkScheduleV1.cost operation = Result.ok cost) :
    bulksketch.decode.stages.Execution.charge field kernels meter operation =
      Result.ok (chargeResult meter cost) := by
  rw [charge_refines field kernels meter operation, priced, bind_ok]

theorem reconstruct_refines : ReconstructChargeRefines := by
  intro F K field kernels meter capacity
  exact charge_refines_with_cost field kernels meter (.Reconstruct capacity)
    (WorkSchedule.reconstructCost capacity) (WorkSchedule.reconstruct_refines capacity)

end BulksketchBridge.StageCharge
