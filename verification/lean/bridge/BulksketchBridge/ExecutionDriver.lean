import Arithmetic.ExecutionDriverGenerated

namespace BulksketchBridge.ExecutionDriver

open Aeneas Aeneas.Std ExecutionDriverRuntime
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (run_next next_stage)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

abbrev RunFrame (F K : Type) :=
  core.result.Result RowProgress DecodeError × Execution F K × RowWorkspace ×
    (RowWorkspace → RowWorkspace) × WorkMeter

def progress {F K : Type} (stage : Stage) (self : Execution F K) : RowProgress :=
  ⟨stage, self.degree, self.hits, self.roots.attempts, self.roots.gcd_degree⟩

/-- Commit the exact lower-stage result into the source row state. A Rust
    decoder failure still returns progress. A DecodeError is latched and
    returned with the updated workspace and meter. -/
def transition {F K : Type} (stage : Stage) (lower : Frame F K) : RunFrame F K :=
  let (reply, self, workspace, back, meter) := lower
  match reply with
  | .Err error => (.Err error, { self with state := .Error error }, workspace, back, meter)
  | .Ok (.Err reason) => (.Ok (progress stage self), { self with state := .Failed reason }, workspace, back, meter)
  | .Ok (.Ok none) => (.Ok (progress stage self), { self with state := .Complete }, workspace, back, meter)
  | .Ok (.Ok (some next)) => (.Ok (progress stage self), { self with state := .Running next }, workspace, back, meter)

def expectedRunNext (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem)
    (canonicalize : Canonicalize) {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (self : Execution F K) (input : RowInput)
    (workspace : RowWorkspace) (meter : WorkMeter) : Result (RunFrame F K) :=
  match self.state with
  | .Running stage => do
    let lower ← Execution.execute calls division canonicalize field kernels self stage input workspace meter
    .ok (transition stage lower)
  | .Error error => .ok (.Err error, self, workspace, id, meter)
  | .Complete => .fail .panic
  | .Failed _ => .fail .panic

def ActualRunNext : Prop :=
  ∀ (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem) (canonicalize : Canonicalize)
    {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (self : Execution F K) (input : RowInput) (workspace : RowWorkspace) (meter : WorkMeter),
    run_next calls division canonicalize field kernels self input workspace meter =
      expectedRunNext calls division canonicalize field kernels self input workspace meter

theorem run_next_refines : ActualRunNext := by
  intro calls division canonicalize F K field kernels self input workspace meter
  cases state : self.state with
  | Complete => simp only [run_next, expectedRunNext, state]
  | Failed reason => simp only [run_next, expectedRunNext, state]
  | Error error =>
    simp only [run_next, expectedRunNext, state]
    rfl
  | Running stage =>
    simp only [run_next, expectedRunNext, state]
    congr 1
    funext frame
    rcases frame with ⟨reply, after, written, back, paid⟩
    cases reply with
    | Err error => rfl
    | Ok lower =>
      cases lower with
      | Err reason => rfl
      | Ok next => cases next <;> rfl

def stageOption : State → Option Stage
  | .Running stage => some stage
  | _ => none

def ActualNextStage : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (self : Execution F K), next_stage field kernels self = .ok (stageOption self.state)

theorem next_stage_refines : ActualNextStage := by
  intro F K field kernels self
  cases state : self.state <;> simp only [next_stage, stageOption, state]

#print axioms run_next_refines
#print axioms next_stage_refines

end BulksketchBridge.ExecutionDriver
