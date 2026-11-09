import Arithmetic.RootEnumerateGenerated
import BulksketchBridge.RootEnumeratePrice
import BulksketchBridge.ClosedLeafAdvance
import BulksketchBridge.ClosedLeafWindows
import BulksketchBridge.BmEntry

namespace BulksketchBridge.RootEnumerate

open Aeneas Aeneas.Std Result
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open ClosedLeafAdvance DenseCoefficient RebuiltLfsr BmEntry
open Aeneas.Std.RootEnumerateRuntime

set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

/-- The actual extracted enumeration call may write both mutable windows on
either Rust Result branch. The count of a successful call fits in the tail. -/
def CandidateLaw {F K : Type} (enumerate : Enumerate) (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (roots : Roots) (workspace : RowWorkspace)
    (directions : Array U64 64#usize) : Prop :=
  ∃ reply candidates bm,
    enumerate field kernels (prefixSlice workspace.polynomials (roots.degree.val + 1)) roots.affine_base
      (prefixSlice directions.to_slice roots.affine_rank.val)
      (tail workspace.roots roots.count.val) workspace.bm = .ok (reply, candidates, bm) ∧
    candidates.length = workspace.roots.length - roots.count.val ∧ bm.length = workspace.bm.length ∧
    ∀ found, reply = .Ok found → found.val ≤ candidates.length

def chargedOperation (roots : Roots) : bulksketch.decode.work.Charge :=
  .AffineEnumeration roots.degree roots.affine_rank

def updatedWorkspace (roots : Roots) (workspace : RowWorkspace) (candidates bm : Slice U64) : RowWorkspace :=
  { workspace with roots := workspace.roots.setSlice! roots.count.val candidates.val, bm := bm }

def Ready {F K : Type} (enumerate : Enumerate) (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (roots : Roots) (workspace : RowWorkspace) : Prop :=
  roots.degree.val < workspace.polynomials.length ∧ roots.affine_rank.val ≤ 64 ∧
  roots.count.val ≤ workspace.roots.length ∧
  (roots.pending ≠ 0#usize → ∃ frame, PopBounds roots workspace frame) ∧
  ∃ directions, workspace.basis.directions = some directions ∧
    CandidateLaw enumerate field kernels roots workspace directions

/-- Exact original wrapper frame, including charge rejection, propagation of
the callee's error and writes, and the original empty or popping advance. -/
def ActualEnumerateAffine : Prop :=
  ∀ (enumerate : Enumerate) {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (roots : Roots) (workspace : RowWorkspace) (meter : WorkMeter),
    (∀ paid, charge meter (chargedOperation roots) = .ok (.Ok (), paid) →
      Ready enumerate field kernels roots workspace) →
    ∃ charged paid, StageCharge.chargeResult meter (enumerationCost roots.degree roots.affine_rank) =
      (charged, paid) ∧ charge meter (chargedOperation roots) = .ok (charged, paid) ∧
    match charged with
    | .Err error =>
      Roots.enumerate_affine enumerate field kernels roots workspace meter =
        .ok (.Err error, roots, workspace, id, paid)
    | .Ok () =>
      ∃ directions reply candidates bm,
        workspace.basis.directions = some directions ∧
        enumerate field kernels (prefixSlice workspace.polynomials (roots.degree.val + 1)) roots.affine_base
          (prefixSlice directions.to_slice roots.affine_rank.val)
          (tail workspace.roots roots.count.val) workspace.bm = .ok (reply, candidates, bm) ∧
        candidates.length = workspace.roots.length - roots.count.val ∧ bm.length = workspace.bm.length ∧
        let written := updatedWorkspace roots workspace candidates bm
        match reply with
        | .Err reason =>
          Roots.enumerate_affine enumerate field kernels roots workspace meter =
            .ok (.Ok (.Err reason), roots, written, id, paid)
        | .Ok found =>
          ∃ count,
            count.val = roots.count.val + found.val ∧ count.val ≤ workspace.roots.length ∧
            let counted := { roots with count := count }
            if roots.pending = 0#usize then
              Roots.enumerate_affine enumerate field kernels roots workspace meter =
                .ok (.Ok (.Ok .Verification), counted, written, id, paid)
            else
              ∃ frame, PopBounds counted written frame ∧
                let advanced := poppedRoots counted written frame
                Roots.enumerate_affine enumerate field kernels roots workspace meter =
                  .ok (.Ok (.Ok (stageFor advanced)), advanced, poppedWorkspace written frame, id, paid)

private theorem roots_suffix (words : Slice U64) (count : Usize) (bounded : count.val ≤ words.length) :
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut ⟨count⟩ words =
      .ok (tail words count.val, fun updated => words.setSlice! count.val updated.val) := by
  obtain ⟨⟨suffix, back⟩, normal, suffixValue, _, backValue⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut.step_spec ⟨count⟩ words bounded)
  have suffixEq : suffix = tail words count.val := by
    apply Slice.ext
    simpa only [tail, Slice.from_val] using suffixValue
  have backEq : back = (fun updated => words.setSlice! count.val updated.val) := by
    funext replacement
    apply Slice.ext
    simpa only [Slice.setSlice!_val] using backValue replacement
  rw [normal, suffixEq, backEq]

private theorem basis_slice (directions : Array U64 64#usize) (rank : Usize) (bounded : rank.val ≤ 64) :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U64))
      directions { «end» := rank } = .ok (prefixSlice directions.to_slice rank.val) := by
  rw [Array.index_SliceIndexRangeToUsizeSlice, shared_prefix_normal]
  simpa only [Array.length_to_slice, show (64#usize).val = 64 by decide] using bounded

theorem enumerate_affine_refines : ActualEnumerateAffine := by
  intro enumerate F K field kernels roots workspace meter ready
  have chargeMeaning := RootRun.roots_charge_returns meter (chargedOperation roots)
    (enumerationCost roots.degree roots.affine_rank) (enumeration_cost_refines _ _)
  rcases charged : StageCharge.chargeResult meter (enumerationCost roots.degree roots.affine_rank) with ⟨reply, paid⟩
  rw [charged] at chargeMeaning
  simp only [chargedOperation] at chargeMeaning
  refine ⟨reply, paid, rfl, chargeMeaning, ?_⟩
  cases reply with
  | Err error =>
    simp only [Roots.enumerate_affine, chargeMeaning, bind_ok,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    dsimp! only
    simp only [Bind.bind, bind_ok]
    rfl
  | Ok paidUnit =>
    cases paidUnit
    obtain ⟨degreeRoom, rankRoom, countRoom, popRoom, directions, directionsEq, reply, candidates, bm,
      called, candidateLen, bmLen, returnedCount⟩ := ready paid chargeMeaning
    refine ⟨directions, reply, candidates, bm, directionsEq, called, candidateLen, bmLen, ?_⟩
    have cut := ClosedLeaf.inclusive_prefix_normal workspace.polynomials roots.degree degreeRoom
    have basis := basis_slice directions roots.affine_rank rankRoom
    have suffix := roots_suffix workspace.roots roots.count countRoom
    have original :
        Roots.enumerate_affine enumerate field kernels roots workspace meter = (do
          match reply with
          | .Err reason => Result.ok (.Ok (.Err reason), roots, updatedWorkspace roots workspace candidates bm, id, paid)
          | .Ok found =>
            let count ← roots.count + found
            let (stage, next, written, back) ← Roots.advance { roots with count := count }
              (updatedWorkspace roots workspace candidates bm)
            Result.ok (.Ok (.Ok stage), next, written, back, paid)) := by
      simp only [Roots.enumerate_affine, chargeMeaning, bind_ok,
        core.result.Result.Insts.CoreOpsTry.branch]
      dsimp! only
      simp only [core.slice.index.Slice.index, cut, RootEnumerateRuntime.optionAsRef,
        directionsEq, bind_ok, core.option.Option.expect,
        Slice.index_mut_SliceIndexRangeFromUsizeSliceInst, suffix]
      dsimp! only
      simp only [basis, bind_ok, called]
      dsimp! only
      cases reply with
      | Ok _ => simp only [updatedWorkspace]
      | Err _ =>
        simp only [updatedWorkspace]
        rfl
    cases reply with
    | Err reason => exact original
    | Ok found =>
      have foundRoom := returnedCount found rfl
      have within : roots.count.val + found.val ≤ workspace.roots.length := by omega
      obtain ⟨count, added, countValue⟩ := RawMulTable.normal_of_spec _ _
        (Usize.add_spec (x := roots.count) (y := found) (within.trans workspace.roots.length_ineq))
      refine ⟨count, countValue, by rwa [countValue], ?_⟩
      dsimp only
      rw [original]
      simp only [added, bind_ok]
      by_cases empty : roots.pending = 0#usize
      · rw [ite_eq_left empty]
        have advanced := advance_empty_refines { roots with count := count }
          (updatedWorkspace roots workspace candidates bm) empty
        rw [advanced]
        simp only [bind_ok]
        rfl
      · rw [ite_eq_right empty]
        obtain ⟨frame, bounds⟩ := popRoom empty
        have admitted : PopBounds { roots with count := count }
            (updatedWorkspace roots workspace candidates bm) frame := bounds
        refine ⟨frame, admitted, ?_⟩
        rw [advance_pop_refines _ _ _ admitted, bind_ok]
        rfl

end BulksketchBridge.RootEnumerate
