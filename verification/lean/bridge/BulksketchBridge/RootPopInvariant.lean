import BulksketchBridge.RootTraversalInvariant

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096

/-- After a source emission and exact pop, the lower live stack still
    represents the same pending factors. The restored factor becomes the
    active factor, while the appended root words represent the prior one. -/
theorem traversal_invariant_after_pop (locator : Polynomial Field) (roots after : Roots)
    (workspace written : RowWorkspace) (capacity budget : Nat) (frame : FactorFrame)
    (before : RootTraversalInvariant locator roots workspace capacity budget)
    (hasPending : 0 < roots.pending.val)
    (top : workspace.stack.val[roots.pending.val - 1]? = some frame)
    (afterDegree : after.degree.val = frame.coefficient_len.val - 1)
    (afterPending : after.pending.val = roots.pending.val - 1)
    (stride : after.stride = roots.stride)
    (count : roots.count.val ≤ after.count.val)
    (widths : workspaceLengths written = workspaceLengths workspace)
    (stack : written.stack = workspace.stack) (factors : written.factors = workspace.factors)
    (active : activeFactor after written = pendingFactor workspace frame)
    (layout : PendingLayout after written.stack written.factors.length written.polynomials.length)
    (mass : factorDegreeMass after written.stack = factorDegreeMass roots workspace.stack)
    (product : traversalProduct false after written = traversalProduct false roots workspace) :
    RootTraversalInvariant locator after written capacity budget := by
  obtain ⟨sized, budgeted, _, represented, exactMass, strideBound, live, noEmpty, _, pending⟩ := before
  have oldPositive : 0 < roots.degree.val := by
    apply Nat.pos_of_ne_zero
    intro zero
    have empty := noEmpty zero
    rw [empty] at hasPending
    exact Nat.not_lt_zero 0 hasPending
  obtain ⟨actual, exactTop, positive, factor⟩ := pending (roots.pending.val - 1) (by omega)
  have same := Option.some.inj (exactTop.symm.trans top)
  subst actual
  have afterPositive : 0 < after.degree.val := by rw [afterDegree]; omega
  have factorValid : ValidFactor (activeFactor after written) after.degree.val := by
    rw [active, afterDegree]
    exact factor
  have represented' : activeTraversalProduct after written = locator := by
    unfold activeTraversalProduct
    rw [ite_eq_right (Nat.ne_of_gt afterPositive), product]
    unfold activeTraversalProduct at represented
    rwa [ite_eq_right (Nat.ne_of_gt oldPositive)] at represented
  have nextLive : liveDegree after written.stack < after.stride.val := by
    rw [stride]
    exact (live_degree_does_not_grow roots after workspace.stack written.stack mass count).trans_lt live
  refine ⟨budget_buffers_same_lengths workspace written capacity budget sized widths, budgeted,
    layout, represented', mass.trans exactMass, by rwa [stride], nextLive,
    (fun zero => (Nat.ne_of_gt afterPositive zero).elim), (fun _ => factorValid), ?_⟩
  intro slot inStack
  have earlier : slot < roots.pending.val := by omega
  obtain ⟨previous, read, length, valid⟩ := pending slot earlier
  have exactFrame : pendingFactor written previous = pendingFactor workspace previous := by
    unfold pendingFactor pendingCoefficients
    rw [factors]
  exact ⟨previous, by rwa [stack], length, exactFrame.symm ▸ valid⟩

#print axioms traversal_invariant_after_pop

end BulksketchBridge.RootRun
