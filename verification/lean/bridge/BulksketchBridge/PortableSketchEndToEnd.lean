import BulksketchBridge.PortableRowEndToEnd
import BulksketchBridge.PortableFrozenSketchBoundary

namespace BulksketchBridge.PortableDecoder

open Aeneas.Std PortableSketchBoundary RebuiltLfsr RootRun ExecutionDriver
open bulksketch.decode.row bulksketch.decode.scratch bulksketch.decode.stages
open bulksketch.types
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels (xor_assign)
open bulksketch.decode.stages.BinaryDecoder.Insts.BulksketchDecodeRowRowDecoderFKExecution (begin)
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (finish)
open scoped symmDiff

set_option maxRecDepth 4096

/-- One bucket's returned IDs are witnessed by calls to the original
Portable XOR, binary row constructor, and native row finish. -/
def PortableBucketRun (left right : NativeSketch) (beta : Usize)
    (workspace : RowWorkspace) (meter : WorkMeter) (bucket : Nat) (output : List U64) : Prop :=
  let zeroDiff := Bool.xor (rowZero left bucket) (rowZero right bucket)
  let budget := rowBudget beta zeroDiff
  ∃ (difference : Slice U64)
    (execution : Execution bulksketch.field.Gf64 bulksketch.backend.portable.Portable)
    (result : RowResult) (written : RowWorkspace) (paid : WorkMeter),
    let input : RowInput := ⟨difference, Slice.from [] (by simp)⟩
    xor_assign portableField (rowWords left bucket) (rowWords right bucket) = .ok difference ∧
    begin portableField portableKernels budget = .ok execution ∧
    finish nativeCalls nativeDivRem nativeCanonicalize portableField portableKernels
      execution input workspace meter = .ok (.Ok result, written, id, paid) ∧
    decodedIds zeroDiff result = some output ∧ paid.limit = meter.limit ∧ paid.exhausted = false ∧
    paid.used.val ≤ meter.used.val + rowWork (rowWidth left.state.shape bucket) budget

private theorem row_width_fits (shape : NativeShape) (bucket : Nat)
    (inside : bucket < shape.capacities.length) : rowWidth shape bucket ≤ 65535 := by
  have inList : bucket < shape.capacities.val.length := inside
  have inMap : bucket < (capacities shape).length := by
    simpa only [capacities, List.length_map] using inList
  unfold rowWidth
  rw [← List.Inhabited_getElem_eq_getElem! _ _ inMap]
  simp only [capacities, List.getElem_map]
  have bound := shape.capacities.val[bucket].hBounds
  change shape.capacities.val[bucket].val < 65536 at bound
  omega

/-- Two valid original frozen sketches of the same shape reconcile
bucket by bucket through the original Portable row decoder. The
concatenated source results represent exactly the whole difference. -/
def ActualPortableFrozenSketchEndToEnd : Prop :=
  ∀ (leftIds rightIds : Finset U64) (left right : NativeSketch) (beta : Usize)
    (workspace : Nat → RowWorkspace) (meter : Nat → WorkMeter),
    ValidFrozenSketch leftIds left → ValidFrozenSketch rightIds right →
    left.state.shape = right.state.shape →
    let shape := left.state.shape
    let count := shape.capacities.length
    (∀ bucket < count,
      let budget := rowBudget beta (Bool.xor (rowZero left bucket) (rowZero right bucket))
      (routedIds count bucket (leftIds ∆ rightIds)).card ≤ beta.val ∧ beta.val ≤ rowWidth shape bucket ∧
      WorkspaceAdmission.Admitted (workspaceLengths (workspace bucket)) (rowWidth shape bucket) budget.nonzero.val ∧
      (meter bucket).exhausted = false ∧
      (meter bucket).used.val + rowWork (rowWidth shape bucket) budget ≤ (meter bucket).limit.val) →
    ∃ rows : Nat → List U64,
      (∀ bucket < count, PortableBucketRun left right beta (workspace bucket) (meter bucket) bucket (rows bucket)) ∧
      let output := (List.range count).flatMap rows
      output.Nodup ∧ output.toFinset = leftIds ∆ rightIds ∧
      ∀ bucket < count, ∀ id ∈ rows bucket, ∃ routed : Usize,
        bulksketch.sketch.shape.SketchShape.bucket_for portableField shape id = .ok routed ∧
        routed.val = bucket

theorem portable_frozen_sketch_end_to_end : ActualPortableFrozenSketchEndToEnd := by
  classical
  intro leftIds rightIds left right beta workspace meter leftValid rightValid sameShape shape count admitted
  have each (bucket : Nat) (inside : bucket < count) :
      ∃ output, PortableBucketRun left right beta (workspace bucket) (meter bucket) bucket output ∧
        output.Nodup ∧ output.toFinset =
          routedIds count bucket leftIds ∆ routedIds count bucket rightIds := by
    have rightInside : bucket < right.state.shape.capacities.length := by rw [← sameShape]; exact inside
    have leftRow := valid_frozen_row leftIds left leftValid bucket inside
    have rightRow := valid_frozen_row rightIds right rightValid bucket rightInside
    rw [← sameShape] at rightRow
    have leftWidth : (rowWords left bucket).length = rowWidth shape bucket :=
      rowWords_length leftIds left leftValid bucket inside
    have rightWidth : (rowWords right bucket).length = rowWidth shape bucket := by
      rw [rowWords_length rightIds right rightValid bucket rightInside, ← sameShape]
    have sameWidth : (rowWords left bucket).length = (rowWords right bucket).length :=
      leftWidth.trans rightWidth.symm
    obtain ⟨size, betaFits, scratch, active, reserve⟩ := admitted bucket inside
    have fits : (routedIds count bucket leftIds ∆ routedIds count bucket rightIds).card ≤ beta.val := by
      rwa [← routed_symmDiff]
    obtain ⟨difference, execution, result, written, paid, output, xorRun, began, finished, decoded,
      unique, exactIds, limit, paidLive, debit⟩ :=
        portable_row_end_to_end (routedIds count bucket leftIds) (routedIds count bucket rightIds)
          (rowWords left bucket) (rowWords right bucket) (rowZero left bucket) (rowZero right bucket)
          beta (workspace bucket) (meter bucket) leftRow rightRow sameWidth
          (by rw [leftWidth]; exact leftValid.capacitiesPositive bucket inside)
          (by rw [leftWidth]; exact row_width_fits shape bucket inside)
          fits (by rwa [leftWidth]) (by rwa [leftWidth]) active (by rwa [leftWidth])
    exact ⟨output, ⟨difference, execution, result, written, paid, xorRun, began, finished,
      decoded, limit, paidLive, by rwa [leftWidth] at debit⟩, unique, exactIds⟩
  let rows := fun bucket => if h : bucket < count then Classical.choose (each bucket h) else []
  have result (bucket : Nat) (inside : bucket < count) :
      PortableBucketRun left right beta (workspace bucket) (meter bucket) bucket (rows bucket) ∧
      (rows bucket).Nodup ∧ (rows bucket).toFinset =
        routedIds count bucket leftIds ∆ routedIds count bucket rightIds := by
    simpa only [rows, dite_eq_left inside] using Classical.choose_spec (each bucket inside)
  exact ⟨rows, fun bucket inside => (result bucket inside).1,
    native_routed_rows_lift portableField shape leftIds rightIds rows leftValid.bucketsPositive
      (fun bucket inside => (result bucket inside).2)⟩

#print axioms portable_frozen_sketch_end_to_end

end BulksketchBridge.PortableDecoder
