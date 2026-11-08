import BulksketchBridge.WorkScheduleSpec
import BulksketchBridge.WorkMeterSpec

namespace BulksketchBridge.StageCharge

open Aeneas.Std

abbrev ChargeResult := core.result.Result Unit bulksketch.types.DecodeError × bulksketch.types.WorkMeter

/-- Reconstitute all three source meter fields from the finite-word model. -/
def meterOfModel (meter : WorkMeter.ModelMeter) : bulksketch.types.WorkMeter :=
  { limit := ⟨meter.limit.toBitVec⟩, used := ⟨meter.used.toBitVec⟩, exhausted := meter.exhausted }

/-- Pricing errors precede meter mutation. A successful price is submitted to
the existing finite-word meter model, including its sticky exhaustion flag. -/
def chargeResult (meter : bulksketch.types.WorkMeter) (cost : WorkSchedule.CostResult) : ChargeResult :=
  match cost with
  | .Err error => (.Err error, meter)
  | .Ok amount =>
    let outcome := (WorkMeter.toModel meter).charge (WorkMeter.toUInt64 amount)
    (WorkMeter.rustOutcome outcome.2, meterOfModel outcome.1)

def reconstructCharge (meter : bulksketch.types.WorkMeter) (capacity : Usize) : ChargeResult :=
  chargeResult meter (WorkSchedule.reconstructCost capacity)

/-- The source wrapper preserves every pricing control result. Any normal
price is submitted to the finite-word charge model. -/
def ChargeRefines : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : bulksketch.backend.contract.BulkKernels K F)
    (meter : bulksketch.types.WorkMeter) (operation : bulksketch.decode.work.Charge),
    bulksketch.decode.stages.Execution.charge field kernels meter operation = (do
      let cost ← bulksketch.decode.work.WorkScheduleV1.cost operation
      .ok (chargeResult meter cost))

/-- The source reconstruction charge returns the exact Rust result and meter
state for every capacity and meter, including overflow and prior exhaustion. -/
def ReconstructChargeRefines : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : bulksketch.backend.contract.BulkKernels K F)
    (meter : bulksketch.types.WorkMeter) (capacity : Usize),
    bulksketch.decode.stages.Execution.charge field kernels meter (.Reconstruct capacity) =
      .ok (reconstructCharge meter capacity)

end BulksketchBridge.StageCharge
