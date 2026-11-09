import BulksketchBridge.RootReducerInvariant
import BulksketchBridge.RootTraversalFactor
import BulksketchBridge.RootTraceInvariant

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial DenseCoefficient SliceKernels RootTrace DenseReducerAlgebra
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096

/-- The original reducer prepares the table and retains the direction
cache required by the first non-affine Trace. -/
def ActualNativeFirstTraceEntry : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid : WorkMeter) (capacity budget : Nat),
    RootTraversalInvariant locator roots workspace capacity budget → 3 ≤ roots.degree.val →
    roots.affine = false → roots.direction.val = 0 → workspace.basis.directions = none →
    TimesXMod.ExactScaleXor kernels → charge meter (.Table roots.degree) = .ok (.Ok (), paid) →
    ∃ written,
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .ReducerPreparation workspace meter =
        .ok (.Ok (.Ok .Trace), roots, written, id, paid) ∧
      RootTraversalInvariant locator roots written capacity budget ∧
      written.basis = workspace.basis ∧
      activeFactor roots written = activeFactor roots workspace ∧
      let buffers := buffersFor roots written
      CorrectTable buffers.modulus buffers.table roots.degree.val ∧
      cacheWellFormed roots buffers ∧
      TraceAgreement (activeFactor roots written) roots.splitter_seed roots.direction.val ∧
      traversalRank .Trace roots written < traversalRank .ReducerPreparation roots workspace

theorem native_first_trace_entry : ActualNativeFirstTraceEntry := by
  intro K kernels locator roots workspace meter paid capacity budget invariant minimum affine direction empty scale charged
  obtain ⟨written, ran, retained, table, decreases⟩ :=
    native_reducer_invariant kernels locator roots workspace meter paid capacity budget invariant minimum scale charged
  have cap := traversal_degree_budget locator roots workspace capacity budget invariant
  have monic := traversal_monic_word locator roots workspace capacity budget invariant (by omega)
  obtain ⟨tableWords, work, exactRan, _, _, _, sameFactor⟩ :=
    native_reducer_preparation kernels roots workspace meter paid capacity budget invariant.buffers minimum cap
      scale charged monic
  let rebuilt := rebuild workspace roots { buffersFor roots workspace with table := tableWords, work }
  have same : written = rebuilt := by
    exact congrArg (fun result : Frame => result.2.2.1) (Result.ok_injective (ran.symm.trans exactRan))
  have sameBasis : written.basis = workspace.basis := by rw [same]; rfl
  have cache : cacheWellFormed roots (buffersFor roots written) := by
    intro basis present
    change written.basis.directions = some basis at present
    rw [sameBasis, empty] at present
    cases present
  have history : TraceAgreement (activeFactor roots written) roots.splitter_seed roots.direction.val := by
    intro earlier active
    omega
  have stage : tableStage roots = .Trace := by simp [tableStage, affine]
  rw [stage] at ran decreases
  exact ⟨written, ran, retained, sameBasis, same.symm ▸ sameFactor, table, cache, history, decreases⟩

#print axioms native_first_trace_entry

end BulksketchBridge.RootRun
