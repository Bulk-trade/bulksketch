import BulksketchBridge.NativeDeflateOuterLoop
import BulksketchBridge.BmEntry
import BulksketchBridge.StageCharge

namespace BulksketchBridge.Deflation

open Aeneas Aeneas.Std Result DenseCoefficient RebuiltLfsr SliceKernels
open bulksketch.backend.contract bulksketch.decode.scratch bulksketch.decode.stages
open bulksketch.decode.row bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

abbrev NativeDeflateResult (K : Type) :=
  (core.result.Result (core.result.Result (Option Stage) DecodeFailure) DecodeError) ×
    Execution bulksketch.field.Gf64 K × RowWorkspace × (RowWorkspace → RowWorkspace) × WorkMeter

def workspaceFromParts (parts : WorkspaceParts) : RowWorkspace :=
  let (syndromes, bm, polynomials, factors, squareTable, verification, roots, raw, stack, basis) := parts
  { syndromes, bm, polynomials, factors, square_table := squareTable, verification, roots, raw, stack, basis }

@[simp] theorem workspace_round_trip (workspace : RowWorkspace) :
    workspaceFromParts (workspaceParts workspace) = workspace := by
  cases workspace
  rfl

def wrapDeflate {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (meter : WorkMeter) (result : Result DeflateAnswer) : Result (NativeDeflateResult K) := do
  let (reply, roots, workspace, back) ← result
  .ok (.Ok reply, { self with roots := roots }, workspace, fun w => workspaceFromParts (back w), meter)

def DeflateBounds {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (input : RowInput) (workspace : RowWorkspace) : Prop :=
  2 * (input.difference.length + 1) ≤ workspace.bm.length ∧
    self.degree.val ≤ input.difference.length ∧
    self.hits.val ≤ self.degree.val ∧ self.hits.val ≤ workspace.roots.length

def deflateFrame {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (workspace : RowWorkspace) (width : Nat) : DeflateFrame :=
  ⟨self.roots, workspace, BmEntry.splitBack workspace.bm width,
    restorePrefix (BmEntry.tail workspace.bm width)⟩

/-- The original native wrapper has two observable branches. The charge
failure returns the untouched state and workspace with its actual updated
meter. A successful charge passes the original BM windows and exactly the
recorded hits to the checked synthetic-division trace. -/
def ActualNativeDeflate : Prop :=
  ∀ {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (_mul : ∀ a b, kernels.ArithmeticInst.mul a b = .ok (mulWord a b))
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput)
    (workspace : RowWorkspace) (meter : WorkMeter) (cost : WorkSchedule.CostResult),
    bulksketch.decode.work.WorkScheduleV1.cost (.Deflate self.degree) = .ok cost →
    ((StageCharge.chargeResult meter cost).1 = .Ok () → DeflateBounds self input workspace) →
    match StageCharge.chargeResult meter cost with
    | (.Err error, meter1) =>
      Execution.deflate field kernels self input workspace meter =
        .ok (.Err error, self, workspace, id, meter1)
    | (.Ok (), meter1) =>
      let width := input.difference.length + 1
      ∃ result : Result DeflateAnswer,
        DeflateTrace (deflateFrame self workspace width) (prefixSlice workspace.roots self.hits.val) 0
          (prefixSlice workspace.bm width) (prefixSlice (BmEntry.tail workspace.bm width) width)
          self.degree result ∧
        Execution.deflate field kernels self input workspace meter = wrapDeflate self meter1 result

theorem native_deflate : ActualNativeDeflate := by
  intro K field kernels mul self input workspace meter cost priced admitted
  have charged := StageCharge.charge_refines_with_cost field kernels meter (.Deflate self.degree) cost priced
  cases chargeEq : StageCharge.chargeResult meter cost with
  | mk response finalMeter =>
    rw [chargeEq] at charged
    cases response with
    | Err error =>
      simp only [Execution.deflate, charged, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      rfl
    | Ok empty =>
      cases empty
      have ready : (StageCharge.chargeResult meter cost).1 = .Ok () := by rw [chargeEq]
      obtain ⟨bmRoom, degreeRoom, hitsRoom, rootRoom⟩ := admitted ready
      have bmMax : workspace.bm.length ≤ Usize.max := Slice.length_ineq workspace.bm
      have capacity := Slice.len_val input.difference
      obtain ⟨width, added, widthVal⟩ := RawMulTable.normal_of_spec _ _
        (Usize.add_spec (x := Slice.len input.difference) (y := 1#usize)
          (by change (Slice.len input.difference).val + 1 ≤ Usize.max; omega))
      have widthValue : width.val = input.difference.length + 1 := by
        change width.val = (Slice.len input.difference).val + 1 at widthVal
        omega
      let tail := BmEntry.tail workspace.bm width.val
      let loc := prefixSlice workspace.bm width.val
      let quo := prefixSlice tail width.val
      let roots := prefixSlice workspace.roots self.hits.val
      let frame := deflateFrame self workspace width.val
      have tailLen : tail.length = workspace.bm.length - width.val := BmEntry.tail_length _ _
      have locLen : loc.length = width.val := by
        change (prefixSlice workspace.bm width.val).length = _
        rw [prefix_length, Nat.min_eq_left (by omega)]
      have quoLen : quo.length = width.val := by
        change (prefixSlice tail width.val).length = _
        rw [prefix_length, Nat.min_eq_left (by omega)]
      have rootsLen : roots.length = self.hits.val := by
        change (prefixSlice workspace.roots self.hits.val).length = _
        rw [prefix_length, Nat.min_eq_left rootRoom]
      have divided : core.slice.Slice.split_at_mut workspace.bm width =
          .ok ((loc, tail), BmEntry.splitBack workspace.bm width.val) :=
        BmEntry.split_refines workspace.bm width (by omega)
      have quotientWindow : core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice U64) tail ⟨width⟩ =
          .ok (quo, restorePrefix tail) := prefix_normal tail width (by omega)
      have rootWindow : core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice U64) workspace.roots ⟨self.hits⟩ =
          .ok roots := shared_prefix_normal workspace.roots self.hits rootRoom
      let result := outerLoop field kernels frame (rootCursor roots 0) loc quo self.degree
      have trace : DeflateTrace frame roots 0 loc quo self.degree result :=
        native_deflate_outer field kernels mul frame roots 0 loc quo self.degree (Nat.zero_le _)
          (by omega) (by omega) (by omega)
      refine ⟨result, ?_, ?_⟩
      · simpa only [frame, roots, loc, quo, tail, widthValue] using trace
      · unfold Execution.deflate
        simp only [charged, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        dsimp! only
        simp only [added, bind_ok, divided]
        dsimp! only
        simp only [quotientWindow, bind_ok]
        dsimp! only
        simp only [rootWindow, SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok]
        rfl

#print axioms native_deflate

end BulksketchBridge.Deflation
