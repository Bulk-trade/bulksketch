import BulksketchBridge.NativeTraceNode
import BulksketchBridge.RootNativeLeafInvariant
import BulksketchBridge.RootEmissionPopMetadata
import BulksketchBridge.RootFrontierBudget

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 RootWorkBudget RootTrace
open ExecutionDriver ExecutionDriverRuntime ExecutionFinish ClosedLeafAdvance
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.stages bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

def PendingTraceHistory (roots : Roots) (workspace : RowWorkspace) : Prop :=
  ∀ slot (frame : FactorFrame), slot < roots.pending.val → workspace.stack.val[slot]? = some frame →
    TraceAgreement (pendingFactor workspace frame) roots.splitter_seed frame.next_direction.val

/-- A ready non-affine frontier for the original V1/V2 stage selection.
Its reserve pays every live subtree. The attempt allowance reserves 64
tries for each remaining proper split, including saved siblings. -/
structure NativeTraceFrontier {K : Type} (locator : Polynomial Field) (point : RootDrainState K)
    (capacity budget : Nat) : Prop where
  state : point.execution.state = .Running (stageFor point.execution.roots)
  noProbe : point.execution.degree_probe = none
  traversal : RootTraversalInvariant locator point.execution.roots point.workspace capacity budget
  workspace : WorkspaceAdmission.Admitted (workspaceLengths point.workspace) capacity budget
  nonAffine : point.execution.roots.affine = false
  plain : point.execution.roots.closed_form = false
  history : TraceAgreement (activeFactor point.execution.roots point.workspace)
    point.execution.roots.splitter_seed point.execution.roots.direction.val
  pending : PendingTraceHistory point.execution.roots point.workspace
  cache : cacheWellFormed point.execution.roots (buffersFor point.execution.roots point.workspace)
  attempts : point.execution.roots.attempts.val + 64 * frontierSplits point.execution.roots point.workspace.stack ≤ Usize.max
  live : point.meter.exhausted = false
  reserve : point.meter.used.val + frontierWork point.execution.roots point.workspace.stack ≤ point.meter.limit.val

structure NativeTraceEmitted {K : Type} (locator : Polynomial Field) (point : RootDrainState K)
    (capacity budget : Nat) : Prop where
  state : point.execution.state = .Running .Verification
  noProbe : point.execution.degree_probe = none
  count : point.execution.roots.count.val = locator.natDegree
  factor : emittedProduct point.execution.roots point.workspace = locator
  workspace : WorkspaceAdmission.Admitted (workspaceLengths point.workspace) capacity budget
  live : point.meter.exhausted = false

/-- Pay the original leaf charge, emit its roots, and either restore the
saved frontier and its trace history or enter native Verification. -/
def ActualNativeTraceFrontierLeaf : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    DirectTwo.CorrectArithmetic kernels →
    ∀ (locator : Polynomial Field) (input : RowInput) (before : RootDrainState K) (capacity budget : Nat),
      NativeTraceFrontier locator before capacity budget → before.execution.state = .Running .Leaf →
      before.execution.roots.degree.val ≤ 2 →
      ∃ after : RootDrainState K,
        SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input 1 before after id ∧
        after.execution.budget = before.execution.budget ∧ after.meter.limit = before.meter.limit ∧
        before.meter.used.val ≤ after.meter.used.val ∧
        after.meter.used.val ≤ before.meter.used.val + frontierWork before.execution.roots before.workspace.stack ∧
        (NativeTraceEmitted locator after capacity budget ∨
          NativeTraceFrontier locator after capacity budget ∧
          after.meter.used.val + frontierWork after.execution.roots after.workspace.stack ≤
            before.meter.used.val + frontierWork before.execution.roots before.workspace.stack ∧
          traversalPotential after.execution.roots after.workspace.stack <
            traversalPotential before.execution.roots before.workspace.stack)

theorem native_trace_frontier_leaf : ActualNativeTraceFrontierLeaf := by
  intro canonicalize K kernels arithmetic locator input before capacity budget ready running bounded
  let roots := before.execution.roots
  have reserve : before.meter.used.val + frontierWork roots before.workspace.stack ≤ before.meter.limit.val :=
    ready.reserve
  obtain ⟨amount, price, _, costBound⟩ := native_root_leaf_price roots.degree bounded
  have costRoot : amount.val ≤ rootsEnvelope roots.degree.val :=
    costBound.trans (Nat.le_add_right ..)
  have enough : before.meter.used.val + amount.val ≤ before.meter.limit.val := by
    change before.meter.used.val + (rootsEnvelope roots.degree.val + _) ≤ _ at reserve
    omega
  obtain ⟨paid, charged, used, limit, live⟩ := native_roots_paid_charge before.meter
    (.Leaf roots.degree) amount amount.val price rfl ready.live enough
  obtain ⟨next, afterRoots, written, ran, outcome⟩ := RootLeaf.native_leaf_traversal_step
    kernels locator roots before.workspace before.meter paid capacity budget arithmetic bounded ready.traversal charged
  obtain ⟨_, widths, terminal, continues⟩ := outcome
  let after := advanceRootState before next afterRoots written paid
  have step := native_root_driver_return canonicalize kernels before.execution .Leaf input before.workspace
    before.meter paid (.Ok (.Ok next)) afterRoots written id running ready.noProbe rfl ran
  have chunk : SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
      1 before after id :=
    SuccessfulChunk.step before after after .Leaf (progress .Leaf { before.execution with roots := afterRoots })
      id id 0 running step (.empty after)
  have afterWorkspace : WorkspaceAdmission.Admitted (workspaceLengths written) capacity budget := by
    rw [widths]
    exact ready.workspace
  refine ⟨after, chunk, rfl, limit, by change _ ≤ paid.used.val; omega, ?_, ?_⟩
  · change paid.used.val ≤ before.meter.used.val + frontierWork roots before.workspace.stack
    rw [used]
    exact Nat.add_le_add_left (costRoot.trans (Nat.le_add_right ..)) _
  · by_cases empty : roots.pending = 0#usize
    · obtain ⟨stage, _, finalCount, emitted⟩ := terminal empty
      exact Or.inl ⟨by change State.Running next = _; rw [stage], ready.noProbe, finalCount, emitted, afterWorkspace, live⟩
    · obtain ⟨frame, top, stage, pending, degree, factor, invariant, rank⟩ := continues empty
      have total := ready.traversal.mass.trans_le ready.traversal.degreeBudget
      change factorDegreeMass roots before.workspace.stack ≤ budget at total
      unfold factorDegreeMass at total
      have polys := ready.traversal.buffers.polynomials
      have out := ready.traversal.buffers.roots
      have bounds : RootLeaf.LeafBounds roots before.workspace := ⟨bounded, by omega, by omega⟩
      obtain ⟨restored, present, savedMeta⟩ := native_leaf_pop_metadata kernels roots afterRoots before.workspace written
        next before.meter paid arithmetic bounds ready.traversal.layout charged empty ran
      have same := Option.some.inj (present.symm.trans top)
      subst restored
      have nonempty : 0 < roots.pending.val := Nat.pos_of_ne_zero (fun zero => empty (UScalar.eq_of_val_eq zero))
      obtain ⟨workCredit, attemptCredit⟩ := frontier_pop_reserve roots afterRoots before.workspace.stack written.stack
        frame nonempty pending degree top (fun slot _ => by rw [savedMeta.stack])
      have paidReserve : paid.used.val + frontierWork afterRoots written.stack ≤
          before.meter.used.val + frontierWork roots before.workspace.stack := by
        rw [used]
        omega
      refine Or.inr ⟨⟨by change State.Running next = .Running (stageFor afterRoots); rw [stage], ready.noProbe, invariant, afterWorkspace,
        savedMeta.affine.trans ready.nonAffine, savedMeta.closedForm.trans ready.plain, ?_, ?_, ?_, ?_, live, ?_⟩, paidReserve, rank⟩
      · change TraceAgreement (activeFactor afterRoots written) afterRoots.splitter_seed afterRoots.direction.val
        rw [factor, savedMeta.splitterSeed, savedMeta.direction]
        have earlier : roots.pending.val - 1 < roots.pending.val := by omega
        exact ready.pending _ _ earlier top
      · intro slot saved inRange exactRead
        change slot < afterRoots.pending.val at inRange
        change written.stack.val[slot]? = some saved at exactRead
        rw [savedMeta.stack] at exactRead
        change TraceAgreement (pendingFactor written saved) afterRoots.splitter_seed saved.next_direction.val
        rw [savedMeta.splitterSeed, pendingFactor, pendingCoefficients, savedMeta.factors]
        have earlier : slot < roots.pending.val := by omega
        exact ready.pending slot saved earlier exactRead
      · change cacheWellFormed afterRoots (buffersFor afterRoots written)
        unfold cacheWellFormed
        change ∀ basis, written.basis.directions = some basis →
          1 ≤ written.basis.len.val ∧ written.basis.len.val ≤ 64 ∧
            cachePrefix afterRoots.splitter_seed basis written.basis.len.val
        rw [savedMeta.basis, savedMeta.splitterSeed]
        exact ready.cache
      · change afterRoots.attempts.val + 64 * frontierSplits afterRoots written.stack ≤ Usize.max
        rw [savedMeta.attempts]
        have old : roots.attempts.val + 64 * frontierSplits roots before.workspace.stack ≤ Usize.max := ready.attempts
        omega
      · change paid.used.val + frontierWork afterRoots written.stack ≤ paid.limit.val
        rw [used, limit]
        omega

#print axioms native_trace_frontier_leaf

end BulksketchBridge.RootRun
