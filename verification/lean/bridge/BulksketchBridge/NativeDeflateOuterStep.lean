import BulksketchBridge.NativeDeflateSyntheticStep
import BulksketchBridge.RootSetup
import BulksketchBridge.ClosedLeafWindows

namespace BulksketchBridge.Deflation

open Aeneas Aeneas.Std Result RebuiltLfsr SliceKernels DenseCoefficient
open bulksketch.backend.contract bulksketch.decode.stages.Execution
open bulksketch.decode.scratch bulksketch.decode.roots
open DenseDivision (reverseRange)

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

abbrev RootCursor := core.slice.iter.Iter U64
abbrev DeflateState := RootCursor × Slice U64 × Slice U64 × Usize
abbrev WorkspaceParts :=
  Slice U64 × Slice U64 × Slice U64 × Slice U64 × Slice U64 × Slice U64 × Slice U64 ×
    Slice bulksketch.types.RawProduct × Slice FactorFrame × SplitterBasis
abbrev DeflateAnswer :=
  core.result.Result (Option bulksketch.types.Stage) bulksketch.types.DecodeFailure × Roots ×
    RowWorkspace × (RowWorkspace → WorkspaceParts)

structure DeflateFrame where
  roots : Roots
  workspace : RowWorkspace
  restoreBM : (Slice U64 × Slice U64) → Slice U64
  restoreQ : Slice U64 → Slice U64

def workspaceParts (w : RowWorkspace) : WorkspaceParts :=
  (w.syndromes, w.bm, w.polynomials, w.factors, w.square_table, w.verification,
    w.roots, w.raw, w.stack, w.basis)

def joinedWorkspace (frame : DeflateFrame) (locator quotient : Slice U64) : RowWorkspace :=
  { frame.workspace with bm := frame.restoreBM (locator, frame.restoreQ quotient) }

def rejectOutput (frame : DeflateFrame) (locator quotient : Slice U64) : DeflateAnswer :=
  (.Err .InvalidLocator, frame.roots, joinedWorkspace frame locator quotient, workspaceParts)

def startOutput (frame : DeflateFrame) (locator quotient : Slice U64) (degree : Usize) :
    Result DeflateAnswer := do
  let (stage, roots, workspace, back) ← Roots.start frame.roots degree
    (joinedWorkspace frame locator quotient)
  .ok (.Ok (some stage), roots, workspace, fun w => workspaceParts (back w))

def outerBody {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64) (frame : DeflateFrame)
    (iterator : RootCursor) (locator quotient : Slice U64) (degree : Usize) :
    Result (ControlFlow DeflateState DeflateAnswer) :=
  deflate_loop0.body field kernels frame.restoreBM frame.restoreQ frame.roots
    frame.workspace.syndromes frame.workspace.polynomials frame.workspace.factors
    frame.workspace.square_table frame.workspace.verification frame.workspace.roots
    frame.workspace.raw frame.workspace.stack frame.workspace.basis iterator locator quotient degree

def outerLoop {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64) (frame : DeflateFrame)
    (iterator : RootCursor) (locator quotient : Slice U64) (degree : Usize) :
    Result DeflateAnswer :=
  deflate_loop0 field kernels frame.restoreBM frame.restoreQ iterator frame.roots
    frame.workspace.syndromes frame.workspace.polynomials frame.workspace.factors
    frame.workspace.square_table frame.workspace.verification frame.workspace.roots
    frame.workspace.raw frame.workspace.stack frame.workspace.basis locator quotient degree

theorem outer_loop_eq {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64) (frame : DeflateFrame)
    (iterator : RootCursor) (locator quotient : Slice U64) (degree : Usize) :
    outerLoop field kernels frame iterator locator quotient degree =
      loop (fun (it, loc, quo, d) => outerBody field kernels frame it loc quo d)
        (iterator, locator, quotient, degree) := rfl

theorem outer_exhausted {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64) (frame : DeflateFrame)
    (iterator next : RootCursor) (locator quotient : Slice U64) (degree : Usize)
    (yielded : core.slice.iter.IteratorSliceIter.next iterator = .ok (none, next)) :
    outerBody field kernels frame iterator locator quotient degree =
      (do let output ← startOutput frame locator quotient degree; .ok (.done output)) := by
  simp only [outerBody, deflate_loop0.body, yielded, bind_ok,
    startOutput, joinedWorkspace, workspaceParts]
  try dsimp! only
  rw [Aeneas.Std.bind_assoc]
  congr 1
  funext outcome
  rcases outcome with ⟨stage, roots, workspace, back⟩
  dsimp! only
  rw [bind_ok]

theorem start_output_refines (frame : DeflateFrame) (locator quotient : Slice U64)
    (degree : Usize) (bounded : RootSetup.RootStartBounds degree
      (joinedWorkspace frame locator quotient)) :
    startOutput frame locator quotient degree = (do
      let affine ← if frame.roots.v3 then bulksketch.decode.affine.preferred RootSetup.gf64Dictionary degree
        else .ok false
      let updated := RootSetup.startedRoots frame.roots degree affine
      .ok (.Ok (some (ClosedLeafAdvance.stageFor updated)), updated,
        RootSetup.startedWorkspace degree (joinedWorkspace frame locator quotient), workspaceParts)) := by
  unfold startOutput
  rw [RootSetup.root_start_refines _ _ _ bounded]
  rw [Aeneas.Std.bind_assoc]
  congr 1
  funext affine
  rw [bind_ok]
  rfl

private theorem read_word (words : Slice U64) (i : Usize) (fits : i.val < words.length) :
    Slice.index_usize words i = .ok words[i.val]! := by
  obtain ⟨word, normal, value⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words i fits)
  rw [normal, value, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! words.val i.val fits)

def syntheticOutput (locator quotient : Slice U64) (root : U64) (degree : Usize) : Slice U64 :=
  syntheticFold locator root (degree.val - 1)
    (quotient.setAtNat (degree.val - 1) locator[degree.val]!)

@[simp] theorem synthetic_output_length (locator quotient : Slice U64) (root : U64) (degree : Usize) :
    (syntheticOutput locator quotient root degree).length = quotient.length := by
  unfold syntheticOutput
  rw [synthetic_fold_length, Slice.setAtNat_length]

theorem outer_root {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : ∀ a b, kernels.ArithmeticInst.mul a b = .ok (mulWord a b))
    (frame : DeflateFrame) (iterator next : RootCursor) (locator quotient : Slice U64)
    (root : U64) (degree : Usize)
    (yielded : core.slice.iter.IteratorSliceIter.next iterator = .ok (some root, next))
    (positive : 0 < degree.val) (locatorRoom : degree.val < locator.length)
    (quotientRoom : degree.val ≤ quotient.length) :
    ∃ lower : Usize, lower.val = degree.val - 1 ∧
      let output := syntheticOutput locator quotient root degree
      outerBody field kernels frame iterator locator quotient degree =
        if remainderWord locator output root ≠ 0#u64 then .ok (.done (rejectOutput frame locator output))
        else .ok (.cont (next, restorePrefix locator (prefixSlice output degree.val), output, lower)) := by
  let seeded := quotient.setAtNat (degree.val - 1) locator[degree.val]!
  let output := syntheticOutput locator quotient root degree
  have seedLength : seeded.length = quotient.length := Slice.setAtNat_length ..
  have outputLength : output.length = quotient.length := synthetic_output_length ..
  have run := native_synthetic_loop field kernels mul locator seeded root degree positive (by omega)
    (by rwa [seedLength])
  change deflate_loop0_loop0 field kernels (reverseRange 1#usize degree) locator seeded root =
    .ok output at run
  obtain ⟨lower, subtracted, indexValue, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := degree) (y := 1#usize) (by change 1 ≤ degree.val; omega))
  change lower.val = degree.val - 1 at indexValue
  have written := Reconstruction.update_normal quotient lower locator[degree.val]! (by omega)
  rw [indexValue] at written
  change Slice.update quotient lower locator[degree.val]! = .ok seeded at written
  have reverse :
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        (core.ops.range.Range.Insts.DoubleEndedIterator
        core.iter.range.StepUsize) { start := 1#usize, «end» := degree } =
          .ok (reverseRange 1#usize degree) := rfl
  have readLocator := read_word locator 0#usize (by change 0 < locator.length; omega)
  have readQuotient := read_word output 0#usize (by change 0 < output.length; omega)
  have dest :
      core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice U64)
        locator ⟨degree⟩ = .ok (prefixSlice locator degree.val, restorePrefix locator) :=
    prefix_normal locator degree (by omega)
  have source :
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U64)
        output ⟨degree⟩ = .ok (prefixSlice output degree.val) :=
    shared_prefix_normal output degree (by omega)
  have copy := ClosedLeaf.copy_normal (prefixSlice locator degree.val) (prefixSlice output degree.val)
    (by rw [prefix_length, prefix_length, Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)])
  refine ⟨lower, indexValue, ?_⟩
  change outerBody field kernels frame iterator locator quotient degree =
    if remainderWord locator output root ≠ 0#u64 then .ok (.done (rejectOutput frame locator output))
    else .ok (.cont (next, restorePrefix locator (prefixSlice output degree.val), output, lower))
  simp only [outerBody, deflate_loop0.body, yielded, bind_ok]
  try dsimp! only
  simp only [read_word locator degree locatorRoom, subtracted, bind_ok, written, reverse]
  rw [run]
  simp only [bind_ok, readLocator, readQuotient, mul, lift]
  by_cases nonzero : remainderWord locator output root ≠ 0#u64
  · have branch : (remainderWord locator output root != 0#u64) = true := by simp [nonzero]
    rw [ite_eq_left nonzero]
    change (if remainderWord locator output root != 0#u64 then _ else _) = _
    rw [branch]
    rfl
  · have branch : (remainderWord locator output root != 0#u64) = false := by simp [not_not.mp nonzero]
    rw [ite_eq_right nonzero]
    change (if remainderWord locator output root != 0#u64 then _ else _) = _
    simp only [branch, Bool.false_eq_true, ite_false, dest, bind_ok]
    try dsimp! only
    simp only [source, copy, bind_ok]

#print axioms outer_exhausted
#print axioms start_output_refines
#print axioms outer_root

end BulksketchBridge.Deflation
