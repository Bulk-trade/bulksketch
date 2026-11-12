import Arithmetic.RowDispatchGenerated
import BulksketchBridge.RowConfiguration
import BulksketchBridge.ExecutionDriver

namespace BulksketchBridge.RowDispatch

open Aeneas.Std RowDispatchRuntime ExecutionDriverRuntime
open ExecutionDriver (RunFrame)
open bulksketch.backend.contract bulksketch.sketch.dispatch bulksketch.decode.stages
open bulksketch.decode.probe bulksketch.decode.row bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (run_next)

def mapTag {F K : Type} (tag : Execution F K → DecodeExecution F)
    (call : Result (Execution F K)) : Result (DecodeExecution F) := do
  let after ← call
  .ok (tag after)

def ActualDecodeEnableV3 : Prop :=
  ∀ (d : Dictionaries) {F : Type} (field : bulksketch.field.BinaryField F) (before : DecodeExecution F),
    DecodeExecution.enable_v3 d field before =
      match before with
      | .Probe _ _ => .ok before
      | .Portable row => mapTag .Portable (Execution.enable_v3 field (d.portable field) row)
      | .Pclmul row => mapTag .Pclmul (Execution.enable_v3 field (d.pclmul field) row)
      | .Vpclmul512 row => mapTag .Vpclmul512 (Execution.enable_v3 field (d.vpclmul512 field) row)

theorem decode_enable_v3_refines : ActualDecodeEnableV3 := by
  intro d F field before
  cases before <;> rfl

def ActualDecodeStartDegrees : Prop :=
  ∀ (d : Dictionaries) {F : Type} (field : bulksketch.field.BinaryField F)
    (before : DecodeExecution F) (capacity : Usize),
    DecodeExecution.start_degrees d field before capacity =
      match before with
      | .Probe _ _ => .ok before
      | .Portable row => mapTag .Portable (Execution.start_degrees field (d.portable field) row capacity)
      | .Pclmul row => mapTag .Pclmul (Execution.start_degrees field (d.pclmul field) row capacity)
      | .Vpclmul512 row => mapTag .Vpclmul512 (Execution.start_degrees field (d.vpclmul512 field) row capacity)

theorem decode_start_degrees_refines : ActualDecodeStartDegrees := by
  intro d F field before capacity
  cases before <;> rfl

def ActualDecodeVerificationCount : Prop :=
  ∀ (d : Dictionaries) {F : Type} (field : bulksketch.field.BinaryField F) (before : DecodeExecution F),
    DecodeExecution.verification_count d field before =
      .ok (match before with
        | .Probe probe _ => probe.count
        | .Portable row => row.roots.count
        | .Pclmul row => row.roots.count
        | .Vpclmul512 row => row.roots.count)

theorem decode_verification_count_refines : ActualDecodeVerificationCount := by
  intro d F field before
  cases before <;> rfl

def ActualDecodeNextStage : Prop :=
  ∀ (d : Dictionaries) {F : Type} (field : bulksketch.field.BinaryField F) (before : DecodeExecution F),
    DecodeExecution.next_stage d field before =
      .ok (match before with
        | .Probe probe _ => probe.next
        | .Portable row => ExecutionDriver.stageOption row.state
        | .Pclmul row => ExecutionDriver.stageOption row.state
        | .Vpclmul512 row => ExecutionDriver.stageOption row.state)

theorem decode_next_stage_refines : ActualDecodeNextStage := by
  intro d F field before
  cases before with
  | Probe probe backend => rfl
  | Portable row => exact ExecutionDriver.next_stage_refines field (d.portable field) row
  | Pclmul row => exact ExecutionDriver.next_stage_refines field (d.pclmul field) row
  | Vpclmul512 row => exact ExecutionDriver.next_stage_refines field (d.vpclmul512 field) row

def ActualProbeReject : Prop :=
  ∀ (before : Probe) (capacity : Usize),
    Probe.reject before capacity =
      .ok (if before.pair = false ∧ 2 ≤ capacity.val ∧ 2 ≤ before.budget.nonzero.val then
        { before with next := some .DirectTwo, count := 0#usize, pair := true }
        else { before with next := some .Reconstruction, count := 0#usize })

theorem probe_reject_refines : ActualProbeReject := by
  intro before capacity
  cases pair : before.pair <;> by_cases cap : 2 ≤ capacity.val <;>
    by_cases budget : 2 ≤ before.budget.nonzero.val <;>
    simp [Probe.reject, pair, cap, budget, UScalar.le_equiv]

def ActualDecodeRejectUpper : Prop :=
  ∀ (d : Dictionaries) {F : Type} (field : bulksketch.field.BinaryField F)
    (before : DecodeExecution F) (capacity : Usize),
    DecodeExecution.reject_upper d field before capacity =
      match before with
      | .Probe probe backend => do
        let after ← Probe.reject probe capacity
        .ok (.Probe after backend)
      | .Portable row => mapTag .Portable (Execution.reject_upper field (d.portable field) row capacity)
      | .Pclmul row => mapTag .Pclmul (Execution.reject_upper field (d.pclmul field) row capacity)
      | .Vpclmul512 row => mapTag .Vpclmul512 (Execution.reject_upper field (d.vpclmul512 field) row capacity)

theorem decode_reject_upper_refines : ActualDecodeRejectUpper := by
  intro d F field before capacity
  cases before <;> rfl

def ActualProbeNextStage : Prop :=
  ∀ before : Probe, Probe.next_stage before = .ok before.next

theorem probe_next_stage_refines : ActualProbeNextStage := fun _ => rfl

def ActualProbeCount : Prop :=
  ∀ before : Probe, Probe.impl.count before = .ok before.count

theorem probe_count_refines : ActualProbeCount := fun _ => rfl

abbrev DispatchFrame (F : Type) :=
  core.result.Result RowProgress DecodeError × DecodeExecution F × RowWorkspace ×
    (RowWorkspace → RowWorkspace) × WorkMeter

def mapRun {F K : Type} (tag : Execution F K → DecodeExecution F)
    (call : Result (RunFrame F K)) : Result (DispatchFrame F) := do
  let (reply, after, written, back, paid) ← call
  .ok (reply, tag after, written, back, paid)

/-- The original backend tag chooses the exact native row execution.
A probe supplies only its two original result slices. -/
def ActualDecodeRunNext : Prop :=
  ∀ (d : Dictionaries) (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem)
    (canonicalize : Canonicalize) (probeRun : ProbeRun)
    {F : Type} (field : bulksketch.field.BinaryField F) (before : DecodeExecution F)
    (input : RowInput) (workspace : RowWorkspace) (meter : WorkMeter),
    DecodeExecution.run_next d calls division canonicalize probeRun field before input workspace meter =
      match before with
      | .Probe probe backend => do
        let (reply, after, verification, roots, paid) ←
          probeRun field backend probe input.difference workspace.verification workspace.roots meter
        .ok (reply, .Probe after backend, { workspace with verification, roots }, id, paid)
      | .Portable row => mapRun .Portable
          (run_next calls division canonicalize field (d.portable field) row input workspace meter)
      | .Pclmul row => mapRun .Pclmul
          (run_next calls division canonicalize field (d.pclmul field) row input workspace meter)
      | .Vpclmul512 row => mapRun .Vpclmul512
          (run_next calls division canonicalize field (d.vpclmul512 field) row input workspace meter)

theorem decode_run_next_refines : ActualDecodeRunNext := by
  intro d calls division canonicalize probeRun F field before input workspace meter
  cases before <;> rfl

#print axioms decode_run_next_refines
#print axioms probe_reject_refines

end BulksketchBridge.RowDispatch
