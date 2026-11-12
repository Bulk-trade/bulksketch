import BulksketchBridge.CandidateOuter
import BulksketchBridge.StageCharge
import BulksketchBridge.BmPrice

namespace BulksketchBridge.CandidateOuter

open Aeneas Aeneas.Std Result
open BulksketchBridge.DenseCoefficient BulksketchBridge.RebuiltLfsr BulksketchBridge.BmEntry
open bulksketch.decode.stages bulksketch.decode.row bulksketch.decode.scratch bulksketch.types
open Aeneas.Std.AvxHornerChunkRuntime (ChunkState chunks)

def candidateCost (degree inputs : Usize) : WorkSchedule.CostResult :=
  match WorkSchedule.checkedCost (2 * inputs.val) with
  | .Err error => .Err error
  | .Ok first =>
    match WorkSchedule.checkedCost (degree.val + 1) with
    | .Err error => .Err error
    | .Ok width => WorkSchedule.checkedCost (first.val * width.val)

theorem candidate_cost_refines (degree inputs : Usize) :
    bulksketch.decode.work.WorkScheduleV1.cost (.Candidates degree inputs) =
      .ok (candidateCost degree inputs) := by
  obtain ⟨n, nCall, nValue⟩ := WorkSchedule.number_refines inputs
  obtain ⟨d, dCall, dValue⟩ := WorkSchedule.number_refines degree
  have first := WorkSchedule.mul_refines 2#u64 n
  change bulksketch.decode.work.mul 2#u64 n =
    .ok (WorkSchedule.checkedCost (2 * n.val)) at first
  rw [nValue] at first
  have width := BmPrice.add_refines d 1#u64
  change bulksketch.decode.work.add d 1#u64 =
    .ok (WorkSchedule.checkedCost (d.val + 1)) at width
  rw [dValue] at width
  simp only [bulksketch.decode.work.WorkScheduleV1.cost, nCall, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, first, candidateCost]
  cases WorkSchedule.checkedCost (2 * inputs.val) with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok count =>
    simp only [dCall, bind_ok, width]
    cases WorkSchedule.checkedCost (degree.val + 1) with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok columns =>
      dsimp! only
      rw [bind_ok]
      dsimp! only
      rw [WorkSchedule.mul_refines count columns, bind_ok]
      cases WorkSchedule.checkedCost (count.val * columns.val) <;>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

def CandidateEntryBounds {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (input : RowInput) (workspace : RowWorkspace) : Prop :=
  self.degree.val ≤ input.difference.length ∧
  2 * (input.difference.length + 1) ≤ workspace.bm.length ∧
  self.degree.val ≤ workspace.roots.length ∧ self.hits.val ≤ self.degree.val

abbrev CandidateReply := core.result.Result
  (core.result.Result (Option Stage) DecodeFailure) DecodeError

def completedReply (reject : Bool) : CandidateReply :=
  if reject then .Ok (.Err .InvalidLocator) else .Ok (.Ok (some .Deflation))

def completedExecution {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (count : Usize) (reject : Bool) : Execution bulksketch.field.Gf64 K :=
  if reject then { self with hits := count }
  else { self with hits := count, roots := { self.roots with count := count } }

def candidateEntryModel {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (input : RowInput) (workspace : RowWorkspace) : Reply :=
  let width := input.difference.length + 1
  let locator := prefixSlice workspace.bm width
  let values := prefixSlice (tail workspace.bm width) width
  let cursor : ChunkState U64 := ⟨input.candidates, 0, width⟩
  runChunks (prefixSlice locator (self.degree.val + 1)) self.degree.val
    input.candidates.length cursor self.hits.val workspace.roots values

def candidateWorkspace (input : RowInput) (workspace : RowWorkspace) (roots values : Slice U64) : RowWorkspace :=
  let width := input.difference.length + 1
  let locator := prefixSlice workspace.bm width
  let rest := tail workspace.bm width
  { workspace with
    roots := roots
    bm := splitBack workspace.bm width (locator, restorePrefix rest values) }

/-- Complete native candidate entry including every pricing and meter exit.
The successful charge uses only the source-admitted scratch and degree bounds. -/
def ActualNativeCandidateEntry : Prop :=
  ∀ {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64),
    HornerLaw kernels →
    ∀ (self : Execution bulksketch.field.Gf64 K) (input : RowInput)
      (workspace : RowWorkspace) (meter : WorkMeter),
      let charge := StageCharge.chargeResult meter (candidateCost self.degree input.candidates.len)
      (charge.1 = .Ok () → CandidateEntryBounds self input workspace) →
      match charge with
      | (.Err error, charged) =>
        Execution.candidates RootSetup.gf64Dictionary kernels self input workspace meter =
          .ok (.Err error, self, workspace, id, charged)
      | (.Ok (), charged) =>
        ∃ count roots values reject,
          candidateEntryModel self input workspace = (count.val, roots, values, reject) ∧
          Execution.candidates RootSetup.gf64Dictionary kernels self input workspace meter =
            .ok (completedReply reject, completedExecution self count reject,
              candidateWorkspace input workspace roots values, id, charged) ∧
          roots.length = workspace.roots.length ∧ values.length = input.difference.length + 1 ∧
          count.val ≤ self.degree.val

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem native_candidate_entry : ActualNativeCandidateEntry := by
  intro K kernels horner self input workspace meter
  dsimp only
  intro bounds
  have charge := StageCharge.charge_refines_with_cost RootSetup.gf64Dictionary kernels meter
    (.Candidates self.degree input.candidates.len) (candidateCost self.degree input.candidates.len)
    (candidate_cost_refines self.degree input.candidates.len)
  cases charged : StageCharge.chargeResult meter (candidateCost self.degree input.candidates.len) with
  | mk status updatedMeter =>
    rw [charged] at charge
    cases status with
    | Err error =>
      rw [Execution.candidates, charge, bind_ok]
      dsimp! only
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      change Aeneas.Std.bind (Aeneas.Std.bind (.ok error) fun e =>
        (.ok (.Err e) : Result CandidateReply))
        (fun r => .ok (r, self, workspace, id, updatedMeter)) = _
      rw [bind_ok, bind_ok]
    | Ok paid =>
      cases paid
      obtain ⟨degreeRoom, buffers, rootRoom, valid⟩ := bounds (by rw [charged])
      let widthNat := input.difference.length + 1
      have max : workspace.bm.length ≤ Usize.max := workspace.bm.length_ineq
      have fits : input.difference.len.val + (1#usize).val ≤ Usize.max := by
        rw [Slice.len_val]
        change widthNat ≤ Usize.max
        omega
      obtain ⟨width, nextWidth, widthVal⟩ := RawMulTable.normal_of_spec _ _
        (Usize.add_spec (x := input.difference.len) (y := 1#usize) fits)
      have widthEq : width.val = widthNat := by
        simpa only [Slice.len_val, show (1#usize).val = 1 from Usize.ofNatCore_val_eq _] using widthVal
      let locator := prefixSlice workspace.bm widthNat
      let rest := tail workspace.bm widthNat
      let values := prefixSlice rest widthNat
      let cursor : ChunkState U64 := ⟨input.candidates, 0, widthNat⟩
      have locatorLen : locator.length = widthNat := by
        unfold locator
        rw [prefix_length, Nat.min_eq_left (by omega)]
      have restLen : rest.length = workspace.bm.length - widthNat := tail_length _ _
      have valuesLen : values.length = widthNat := by
        unfold values
        rw [prefix_length, Nat.min_eq_left (by rw [restLen]; omega)]
      have split := split_refines workspace.bm width (by rw [widthEq]; omega)
      have valuesIndex := prefix_normal rest width (by rw [widthEq, restLen]; omega)
      rw [widthEq] at split valuesIndex
      have start : chunks input.candidates width = .ok cursor := by
        unfold chunks
        rw [widthEq, ite_eq_right (by omega)]
      obtain ⟨count, roots, scratch, reject, model, normal, rootsLen, scratchLen, countBound⟩ :=
        native_candidate_outer kernels horner self.degree self.hits locator workspace.roots values cursor
          input.candidates.length (by rw [locatorLen]; omega) rootRoom valid
          (by change 0 < widthNat; omega) (by change widthNat ≤ values.length; omega)
          (by change input.candidates.length - 0 ≤ _; omega)
      refine ⟨count, roots, scratch, reject, model, ?_, rootsLen, scratchLen.trans valuesLen, countBound⟩
      rw [Execution.candidates, charge, bind_ok]
      dsimp! only
      simp only [bind_ok, nextWidth, split]
      dsimp! only
      rw [core.slice.index.Slice.index_mut]
      have indexCall : core.slice.index.SliceIndexRangeToUsizeSlice.index_mut ⟨width⟩
          (tail workspace.bm widthNat) = .ok (values, restorePrefix rest) := valuesIndex
      simp only [indexCall, bind_ok]
      dsimp! only
      rw [start, bind_ok, normal, bind_ok]
      dsimp! only
      cases reject <;> rfl

#print axioms candidate_cost_refines
#print axioms native_candidate_entry

end BulksketchBridge.CandidateOuter
