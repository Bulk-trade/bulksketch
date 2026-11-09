import BulksketchBridge.RootTraversalInvariant
import BulksketchBridge.RootTraversalRanking

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial SliceKernels DenseCoefficient RebuiltLfsr BmEntry
open bulksketch.decode.roots bulksketch.decode.scratch

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

/-- A reborrow of the same factor changes only the working windows. The
emitted prefix, live factors and stored layout survive scratch updates. -/
theorem rebuild_preserves_traversal (locator : Polynomial Field) (roots after : Roots)
    (workspace : RowWorkspace) (updated : FactorWork) (capacity budget : Nat)
    (before : RootTraversalInvariant locator roots workspace capacity budget)
    (sameDegree : after.degree = roots.degree) (samePending : after.pending = roots.pending)
    (sameCount : after.count = roots.count) (sameStride : after.stride = roots.stride)
    (sameAffine : after.affine = roots.affine)
    (reborrow : buffersFor after (rebuild workspace roots updated) = updated)
    (sameModulus : updated.modulus = (buffersFor roots workspace).modulus)
    (rawWidth : updated.raw.length = workspace.raw.length) :
    RootTraversalInvariant locator after (rebuild workspace roots updated) capacity budget := by
  let written := rebuild workspace roots updated
  have widths : workspaceLengths written = workspaceLengths workspace := by
    simp only [written, workspaceLengths, rebuild, RootSetup.restoreWork, splitBack_length, restore_length]
    rw [rawWidth]
  have polyWidth : written.polynomials.length = workspace.polynomials.length :=
    congrArg WorkspaceAdmission.Lengths.polynomials widths
  have activeEq : activeFactor after written = activeFactor roots workspace := by
    change slicePolynomial (buffersFor after written).modulus = _
    rw [reborrow, sameModulus]
    rfl
  have pendingEq : pendingProduct written after.pending.val = pendingProduct workspace roots.pending.val := by
    rw [samePending]
    rfl
  have product : activeTraversalProduct after written = locator := by
    unfold activeTraversalProduct traversalProduct liveProduct
    rw [sameDegree, pendingEq, activeEq]
    have emitted : emittedProduct after written = emittedProduct roots workspace := by
      unfold emittedProduct
      rw [sameCount]
      rfl
    rw [emitted]
    exact before.represented
  have layout : PendingLayout after written.stack written.factors.length written.polynomials.length := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [samePending]
      exact before.layout.stackRoom
    · rw [samePending, sameStride]
      exact before.layout.factorRoom
    · rw [sameStride, polyWidth]
      exact before.layout.polynomialRoom
    · intro slot live
      rw [samePending] at live
      obtain ⟨frame, read, framed⟩ := before.layout.slots slot live
      exact ⟨frame, read, by simpa only [SlotLayout, sameStride, sameAffine] using framed⟩
  refine ⟨budget_buffers_same_lengths workspace written capacity budget before.buffers widths,
    before.degreeBudget, layout, product, ?_, by rw [sameStride]; exact before.stride, ?_, ?_, ?_, ?_⟩
  · unfold factorDegreeMass
    rw [sameDegree, sameCount, samePending]
    exact before.mass
  · unfold liveDegree
    rw [sameDegree, samePending, sameStride]
    exact before.live
  · rw [sameDegree, samePending]
    exact before.zeroActive
  · rw [sameDegree, activeEq]
    exact before.active
  · rw [samePending]
    exact before.pending

#print axioms rebuild_preserves_traversal

end BulksketchBridge.RootRun
