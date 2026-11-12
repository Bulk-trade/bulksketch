import BulksketchBridge.CandidateEntry
import BulksketchBridge.NativeDeflateTraversalEntry

namespace BulksketchBridge.CandidateOuter

open Aeneas.Std Algebra.Gf64 Polynomial SliceKernels DenseCoefficient BmEntry RebuiltLfsr
open Deflation RootRun
open bulksketch.decode.row bulksketch.decode.stages bulksketch.decode.scratch

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- The candidate stage only writes its evaluation half of the BM window.
The original locator prefix stays byte-for-byte unchanged. -/
theorem candidate_locator_frame (input : RowInput) (workspace : RowWorkspace) (roots values : Slice U64)
    (widthRoom : input.difference.length + 1 ≤ workspace.bm.length) :
    prefixSlice (candidateWorkspace input workspace roots values).bm (input.difference.length + 1) =
      prefixSlice workspace.bm (input.difference.length + 1) := by
  let width := input.difference.length + 1
  let locator := prefixSlice workspace.bm width
  let rest := restorePrefix (tail workspace.bm width) values
  have fits : locator.length = min width workspace.bm.length := prefix_length ..
  have restWidth : rest.length = workspace.bm.length - width :=
    (restore_length ..).trans (tail_length ..)
  have exactWidth : locator.length = width := fits.trans (Nat.min_eq_left widthRoom)
  change prefixSlice (splitBack workspace.bm width (locator, rest)) width = locator
  apply Slice.ext
  rw [splitBack, dite_eq_left ⟨fits, restWidth⟩]
  simp only [prefixSlice, Slice.from_val, ← exactWidth]
  exact List.take_left

/-- The exact successful candidate result and its checked ordered support
    supply the native deflation handoff. -/
theorem candidate_support_deflate_handoff {K : Type}
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput) (workspace : RowWorkspace)
    (count : Usize) (roots values : Slice U64) (accepted : List U64)
    (admitted : WorkspaceAdmission.Admitted (workspaceLengths workspace)
      input.difference.length self.budget.nonzero.val)
    (budgetCap : self.budget.nonzero.val ≤ input.difference.length)
    (degreeBound : self.degree.val ≤ self.budget.nonzero.val)
    (pending : self.roots.pending = 0#usize)
    (countBound : count.val ≤ self.degree.val)
    (rootWidth : roots.length = workspace.roots.length)
    (exactCount : count.val = accepted.length)
    (exactRoots : roots.val.take count.val = accepted)
    (distinct : accepted.Nodup)
    (found : ∀ point ∈ accepted,
      (slicePolynomial (prefixSlice workspace.bm (self.degree.val + 1))).IsRoot (toField point.bv))
    (monic : (slicePolynomial (prefixSlice workspace.bm (self.degree.val + 1))).Monic)
    (degree : (slicePolynomial (prefixSlice workspace.bm (self.degree.val + 1))).natDegree = self.degree.val)
    (split : (slicePolynomial (prefixSlice workspace.bm (self.degree.val + 1))).Splits)
    (simple : (slicePolynomial (prefixSlice workspace.bm (self.degree.val + 1))).roots.Nodup)
    (nonzero : ∀ point, (slicePolynomial (prefixSlice workspace.bm (self.degree.val + 1))).IsRoot point → point ≠ 0) :
    let next := completedExecution self count false
    let written := candidateWorkspace input workspace roots values
    DeflateCandidateHandoff next input written ∧ DeflateCandidateMeaning next input written := by
  let next := completedExecution self count false
  let written := candidateWorkspace input workspace roots values
  have layout : workspaceLengths written = workspaceLengths workspace := by
    simp only [workspaceLengths, written, candidateWorkspace, splitBack_length, rootWidth]
  have widthRoom : input.difference.length + 1 ≤ workspace.bm.length := by
    have room := admitted.2.2.2.2.2.2.2.2.1
    change 4 * (input.difference.length + 1) ≤ workspace.bm.length at room
    omega
  have locator : initialDeflateLocator next input written =
      slicePolynomial (prefixSlice workspace.bm (self.degree.val + 1)) := by
    unfold initialDeflateLocator activeLocator
    change slicePolynomial (prefixSlice (prefixSlice written.bm (input.difference.length + 1))
      (self.degree.val + 1)) = _
    rw [candidate_locator_frame input workspace roots values widthRoom, ClosedLeaf.prefix_prefix]
    omega
  have hits : (deflateHits next written).val = accepted := by
    simpa only [deflateHits, next, written, completedExecution, Bool.false_eq_true, ite_false,
      candidateWorkspace, prefixSlice, Slice.from_val] using exactRoots
  refine ⟨⟨budgetCap, degreeBound, countBound, rfl, pending, by rwa [layout]⟩, ?_⟩
  refine ⟨locator.symm ▸ monic, locator.symm ▸ degree, locator.symm ▸ split,
    locator.symm ▸ simple, fun point root => nonzero point (locator ▸ root), ?_, ?_⟩
  · intro index active
    have valid : index < accepted.length := by rwa [← exactCount]
    rw [locator, Slice.getElem!_Nat_eq, hits]
    exact found _ (by rw [← List.Inhabited_getElem_eq_getElem! _ _ valid]; exact List.getElem_mem valid)
  · intro left right ordered active
    have validRight : right < accepted.length := by rwa [← exactCount]
    have validLeft : left < accepted.length := ordered.trans validRight
    rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_eq, hits]
    rw [← List.Inhabited_getElem_eq_getElem! _ _ validLeft, ← List.Inhabited_getElem_eq_getElem! _ _ validRight]
    exact fun equal => (Nat.ne_of_lt ordered) (distinct.getElem_inj_iff.mp equal)

#print axioms candidate_support_deflate_handoff

end BulksketchBridge.CandidateOuter
