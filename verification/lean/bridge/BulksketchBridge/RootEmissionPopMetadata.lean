import BulksketchBridge.RootNativeLeafComplete
import BulksketchBridge.RootNativeAffineEnumerationComplete
import BulksketchBridge.RootPendingLayout

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std Result ClosedLeafAdvance
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- These fields are the original saved pop metadata. A pending child
restores its direction and check bit, and only an affine child restores
a saved base and rank. The row's mode, basis, and earlier pending storage
are kept. -/
structure NativePopMetadata (roots after : Roots) (workspace written : RowWorkspace)
    (frame : FactorFrame) : Prop where
  direction : after.direction = frame.next_direction
  checked : after.checked = (frame.split_checked != 0#u32)
  attempts : after.attempts = roots.attempts
  affine : after.affine = roots.affine
  affineReady : after.affine_ready = roots.affine_ready
  closedForm : after.closed_form = roots.closed_form
  v3 : after.v3 = roots.v3
  splitterSeed : after.splitter_seed = roots.splitter_seed
  stride : after.stride = roots.stride
  basis : written.basis = workspace.basis
  factors : written.factors = workspace.factors
  stack : written.stack = workspace.stack
  affineRestore : roots.affine = true →
    after.affine_base = workspace.factors[frame.coefficient_start.val + roots.stride.val - 1]! ∧
      after.affine_rank.val = frame.next_direction.val
  scalarRestore : roots.affine = false →
    after.affine_base = roots.affine_base ∧ after.affine_rank = roots.affine_rank

private theorem exact_rank_cast (rank : U32) : (UScalar.cast .Usize rank).val = rank.val := by
  have platform : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with width | width
    · simpa only [width] using (show (2 : Nat) ^ 32 ≤ 2 ^ 32 by decide)
    · simpa only [width] using (show (2 : Nat) ^ 32 ≤ 2 ^ 64 by decide)
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (rank.hBounds.trans_le platform)

private theorem modeled_pop_metadata (roots : Roots) (workspace emitted : RowWorkspace)
    (count : Usize) (frame : FactorFrame)
    (basis : emitted.basis = workspace.basis)
    (factors : emitted.factors = workspace.factors) (stack : emitted.stack = workspace.stack) :
    NativePopMetadata roots (poppedRoots {roots with count := count} emitted frame)
      workspace (poppedWorkspace emitted frame) frame := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, basis, factors, stack, ?_, ?_⟩
  · intro affine
    simp only [poppedRoots, affine, ite_true, factors, exact_rank_cast, and_self]
  · intro scalar
    simp only [poppedRoots, scalar, Bool.false_eq_true, ite_false, and_self]

private theorem paid_leaf_model (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter)
    (charged : charge meter (.Leaf roots.degree) = .ok (.Ok (), paid)) :
    RootLeaf.expectedLeaf roots workspace meter =
      match RootLeaf.leafCandidates roots.degree.val workspace.polynomials with
      | .Err reason => .ok (.Ok (.Err reason), roots, workspace, id, paid)
      | .Ok words =>
        if 0#u64 ∈ words.val then .ok (.Ok (.Err .InvalidLocator), roots, workspace, id, paid)
        else RootLeaf.leafResume roots workspace words paid := by
  have complete : RootLeaf.expectedLeaf roots workspace meter = (do
      let (reply, finalMeter) ← charge meter (.Leaf roots.degree)
      match reply with
      | .Err reason => .ok (.Err reason, roots, workspace, id, finalMeter)
      | .Ok () =>
        match RootLeaf.leafCandidates roots.degree.val workspace.polynomials with
        | .Err reason => .ok (.Ok (.Err reason), roots, workspace, id, finalMeter)
        | .Ok words =>
          if 0#u64 ∈ words.val then .ok (.Ok (.Err .InvalidLocator), roots, workspace, id, finalMeter)
          else RootLeaf.leafResume roots workspace words finalMeter) := by
    rw [ClosedLeafAdvance.charge_refines]
    unfold RootLeaf.expectedLeaf
    simp only [Aeneas.Std.bind_assoc, bind_ok]
    rfl
  rw [complete, charged, bind_ok]
  rfl

/-- A successful original ordinary leaf that has a pending frame restores
the exact saved metadata, with its original shared basis and stack. -/
def ActualNativeLeafPopMetadata : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots after : Roots) (workspace written : RowWorkspace) (stage : Stage) (meter paid : WorkMeter),
    DirectTwo.CorrectArithmetic kernels → RootLeaf.LeafBounds roots workspace →
    PendingLayout roots workspace.stack workspace.factors.length workspace.polynomials.length →
    charge meter (.Leaf roots.degree) = .ok (.Ok (), paid) → roots.pending ≠ 0#usize →
    Roots.run nativeCalls nativeDivRem dictionary kernels roots .Leaf workspace meter =
      .ok (.Ok (.Ok stage), after, written, id, paid) →
    ∃ frame, workspace.stack.val[roots.pending.val - 1]? = some frame ∧
      NativePopMetadata roots after workspace written frame

theorem native_leaf_pop_metadata : ActualNativeLeafPopMetadata := by
  intro K kernels roots after workspace written stage meter paid arithmetic bounds layout charged pending native
  rw [original_root_run_refines kernels roots .Leaf workspace meter trivial] at native
  change Roots.leaf DirectTwo.fieldDictionary kernels roots workspace meter = _ at native
  rw [RootLeaf.root_leaf_refines kernels roots workspace meter arithmetic bounds, paid_leaf_model _ _ _ _ charged] at native
  cases candidate : RootLeaf.leafCandidates roots.degree.val workspace.polynomials with
  | Err reason =>
    rw [candidate] at native
    have different := congrArg (fun frame : RootLeaf.LeafFrame => frame.1) (Result.ok_injective native)
    cases core.result.Result.Ok.inj different
  | Ok words =>
    rw [candidate] at native
    dsimp! only at native
    by_cases invalid : 0#u64 ∈ words.val
    · rw [ite_eq_left invalid] at native
      have different := congrArg (fun frame : RootLeaf.LeafFrame => frame.1) (Result.ok_injective native)
      cases core.result.Result.Ok.inj different
    · rw [ite_eq_right invalid] at native
      obtain ⟨frame, pop, _⟩ := pop_bounds_of_pending_layout roots workspace layout pending
      let counted := {roots with count := usizeWord (roots.count.val + roots.degree.val)}
      let emitted := {workspace with roots := workspace.roots.setSlice! roots.count.val words.val}
      have updatedPop : PopBounds counted emitted frame := pop
      unfold RootLeaf.leafResume at native
      dsimp only at native
      rw [advance_pop_refines counted emitted frame updatedPop, bind_ok] at native
      have same := Result.ok_injective native
      have state : poppedRoots counted emitted frame = after := congrArg (fun out : RootLeaf.LeafFrame => out.2.1) same
      have returned : poppedWorkspace emitted frame = written := congrArg (fun out : RootLeaf.LeafFrame => out.2.2.1) same
      rw [← state, ← returned]
      exact ⟨frame, pop.2.1, modeled_pop_metadata roots workspace emitted _ frame rfl rfl rfl⟩

/-- The affine emission wrapper restores the same saved metadata from its
actual popped frame. The normal enumeration callback contract remains
explicit and can be supplied by the verified native enumerator. -/
def ActualNativeAffinePopMetadata : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots after : Roots) (workspace written : RowWorkspace) (stage : Stage) (meter paid : WorkMeter),
    RootEnumerate.Ready bulksketch.decode.affine.enumerate dictionary kernels roots workspace →
    charge meter (RootEnumerate.chargedOperation roots) = .ok (.Ok (), paid) → roots.pending ≠ 0#usize →
    Roots.run nativeCalls nativeDivRem dictionary kernels roots .AffineEnumeration workspace meter =
      .ok (.Ok (.Ok stage), after, written, id, paid) →
    ∃ frame, workspace.stack.val[roots.pending.val - 1]? = some frame ∧
      NativePopMetadata roots after workspace written frame

theorem native_affine_pop_metadata : ActualNativeAffinePopMetadata := by
  intro K kernels roots after workspace written stage meter paid ready charged pending native
  obtain ⟨reply, finalMeter, _, paidNormal, wrapper⟩ := RootEnumerate.enumerate_affine_refines
    bulksketch.decode.affine.enumerate dictionary kernels roots workspace meter (fun _ _ => ready)
  have samePayment := Result.ok_injective (paidNormal.symm.trans charged)
  have replyEq : reply = .Ok () := congrArg Prod.fst samePayment
  have meterEq : finalMeter = paid := congrArg Prod.snd samePayment
  subst reply
  subst finalMeter
  obtain ⟨_, answer, candidates, scratch, _, _, _, _, wrapper⟩ := wrapper
  rw [original_root_run_refines kernels roots .AffineEnumeration workspace meter trivial] at native
  change Roots.enumerate_affine bulksketch.decode.affine.enumerate dictionary kernels roots workspace meter =
    .ok (.Ok (.Ok stage), after, written, id, paid) at native
  cases answer with
  | Err error =>
    have same := Result.ok_injective (native.symm.trans wrapper)
    have reply := congrArg (fun f : RootRun.Frame => f.1) same
    cases core.result.Result.Ok.inj reply
  | Ok found =>
    obtain ⟨count, _, _, resumed⟩ := wrapper
    rw [ite_eq_right pending] at resumed
    obtain ⟨frame, bounds, resumed⟩ := resumed
    let counted := {roots with count := count}
    let emitted := RootEnumerate.updatedWorkspace roots workspace candidates scratch
    have same := Result.ok_injective (native.symm.trans resumed)
    have state : after = poppedRoots counted emitted frame := congrArg (fun f : RootRun.Frame => f.2.1) same
    have out : written = poppedWorkspace emitted frame := congrArg (fun f : RootRun.Frame => f.2.2.1) same
    rw [state, out]
    exact ⟨frame, bounds.2.1, modeled_pop_metadata roots workspace emitted count frame rfl rfl rfl⟩

#print axioms native_leaf_pop_metadata
#print axioms native_affine_pop_metadata

end BulksketchBridge.RootRun
