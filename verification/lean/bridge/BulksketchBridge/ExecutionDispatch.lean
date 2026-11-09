import BulksketchBridge.ExecutionDriver

namespace BulksketchBridge.ExecutionDriver

open Aeneas Aeneas.Std ExecutionDriverRuntime
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.decode.degree_probe bulksketch.types
open core.result.Result.Insts

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

abbrev RootReply := core.result.Result (core.result.Result Stage DecodeFailure) DecodeError
abbrev BmReply := core.result.Result (core.result.Result Usize DecodeFailure) DecodeError

def liftRootReply : RootReply → StageReply
  | .Err error => .Err error
  | .Ok (.Err reason) => .Ok (.Err reason)
  | .Ok (.Ok stage) => .Ok (.Ok (some stage))

def bmFrame {F K : Type} (self : Execution F K) (workspace : RowWorkspace)
    (reply : BmReply) (written : Slice U64) (meter : WorkMeter) : Result (Frame F K) :=
  let workspace := { workspace with bm := written }
  match reply with
  | .Err error => .ok (.Err error, self, workspace, id, meter)
  | .Ok (.Err reason) => .ok (.Ok (.Err reason), self, workspace, id, meter)
  | .Ok (.Ok degree) => do
    let leading ← Slice.index_usize written 0#usize
    let next : core.result.Result (Option Stage) DecodeFailure :=
      if leading = 0#u64 then .Err .InvalidLocator else .Ok (some .CandidateEvaluation)
    .ok (.Ok next, { self with degree }, workspace, id, meter)

def reconstructionNext : Option Stage → Bool
  | some .Reconstruction => true
  | _ => false

def probeFrame {F K : Type} (self : Execution F K) (probe : DegreeProbe)
    (workspace : RowWorkspace) (back : RowWorkspace → RowWorkspace) (meter : WorkMeter)
    (reply : core.result.Result (Option Stage) DecodeError) : Result (Frame F K) :=
  match reply with
  | .Err error => .ok (.Err error, { self with degree_probe := some probe }, workspace, back, meter)
  | .Ok stage => do
    let count ← DegreeProbe.impl.count probe
    let updated := {
      self with
      roots := { self.roots with count }
      degree_probe := if reconstructionNext stage then none else some probe
    }
    .ok (.Ok (.Ok stage), updated, workspace, back, meter)

def expectedExecute (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem)
    (canonicalize : Canonicalize) {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (self : Execution F K) (stage : Stage) (input : RowInput)
    (workspace : RowWorkspace) (meter : WorkMeter) : Result (Frame F K) :=
  match self.degree_probe with
  | some probe => do
    let (reply, updated, written, back, paid) ← DegreeProbe.run field kernels probe input.difference self.budget workspace meter
    probeFrame self updated written back paid reply
  | none =>
    match stage with
    | .Reconstruction => Execution.reconstruct field kernels self input workspace meter
    | .BerlekampMassey => do
      let (reply, bm, paid) ← bulksketch.decode.bm.locator field kernels workspace.syndromes
        input.difference.len self.budget.nonzero workspace.bm meter
      bmFrame self workspace reply bm paid
    | .CandidateEvaluation => Execution.candidates field kernels self input workspace meter
    | .Deflation => Execution.deflate field kernels self input workspace meter
    | .Verification => Execution.verify field kernels self input workspace meter
    | .Canonicalization => canonicalize field kernels self workspace meter
    | _ => do
      let (reply, updated, written, back, paid) ← Roots.run calls division field kernels self.roots stage workspace meter
      .ok (liftRootReply reply, { self with roots := updated }, written, back, paid)

private theorem root_reply {F K : Type} (self : Execution F K) (updated : Roots)
    (written : RowWorkspace) (back : RowWorkspace → RowWorkspace) (paid : WorkMeter) (reply : RootReply) :
    (do
      let cf ← CoreOpsTry.branch reply
      match cf with
      | .Continue value => do
        let mapped ← resultMap (bulksketch.P.Insts.CoreOpsFunctionFnOnceTupleTOption Stage) value someValue
        .ok (.Ok mapped, { self with roots := updated }, written, back, paid)
      | .Break residual => do
        let result ← CoreOpsTry_traitFromResidualResult.from_residual
          (core.result.Result (Option Stage) DecodeFailure) (core.convert.FromSame DecodeError) residual
        .ok (result, { self with roots := updated }, written, back, paid)) =
    Result.ok (liftRootReply reply, { self with roots := updated }, written, back, paid) := by
  cases reply with
  | Err error =>
    simp only [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      Bind.bind, bind_ok, liftRootReply]
  | Ok value =>
    cases value <;>
      simp only [CoreOpsTry.branch, resultMap, bulksketch.P.Insts.CoreOpsFunctionFnOnceTupleTOption,
        someCall, someValue, Bind.bind, bind_ok, liftRootReply]

private theorem reconstruction_test (next : Option Stage) :
    optionEq bulksketch.types.Stage.Insts.CoreCmpPartialEqStage next (some .Reconstruction) =
      .ok (reconstructionNext next) := by
  cases next with
  | none => rfl
  | some stage =>
    cases stage <;> simp [optionEq, reconstructionNext, bulksketch.types.Stage.Insts.CoreCmpPartialEqStage,
      bulksketch.types.Stage.Insts.CoreCmpPartialEqStage.eq, bulksketch.types.Stage.read_discriminant, IScalar.eq_equiv]

def ActualExecute : Prop :=
  ∀ (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem) (canonicalize : Canonicalize)
    {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (self : Execution F K) (stage : Stage) (input : RowInput) (workspace : RowWorkspace) (meter : WorkMeter),
    Execution.execute calls division canonicalize field kernels self stage input workspace meter =
      expectedExecute calls division canonicalize field kernels self stage input workspace meter

theorem execute_refines : ActualExecute := by
  intro calls division canonicalize F K field kernels self stage input workspace meter
  cases probe : self.degree_probe with
  | some initial =>
    simp only [Execution.execute, expectedExecute, probe]
    congr 1
    funext lower
    rcases lower with ⟨reply, updated, written, back, paid⟩
    dsimp! only
    cases reply with
    | Err error =>
      simp only [probeFrame, CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, Bind.bind, bind_ok]
    | Ok next =>
      simp only [probeFrame, CoreOpsTry.branch, bind_ok, reconstruction_test]
      congr 1
      funext count
      cases selected : reconstructionNext next <;> rfl
  | none =>
    cases stage <;> simp only [Execution.execute, expectedExecute, probe] <;> try rfl
    case BerlekampMassey =>
      congr 1
      funext lower
      rcases lower with ⟨reply, bm, paid⟩
      dsimp! only
      cases reply with
      | Err error =>
        simp only [bmFrame, CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, Bind.bind, bind_ok]
        rfl
      | Ok lower =>
        cases lower with
        | Err reason =>
          simp only [bmFrame, CoreOpsTry.branch, bind_ok]
          rfl
        | Ok degree =>
          simp only [bmFrame, CoreOpsTry.branch, bind_ok]
          congr 1
          funext leading
          by_cases zero : leading = 0#u64 <;> simp only [zero, ite_true, ite_false, probe] <;> rfl
    all_goals
      congr 1
      funext lower
      rcases lower with ⟨reply, updated, written, back, paid⟩
      dsimp! only
      have exactReply := root_reply self updated written back paid reply
      rw [probe] at exactReply
      exact exactReply

#print axioms execute_refines

end BulksketchBridge.ExecutionDriver
