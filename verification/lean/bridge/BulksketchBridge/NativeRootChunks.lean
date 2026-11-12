import BulksketchBridge.RankedExecutionChunks
import BulksketchBridge.RankedRootDrainAdapter

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std ExecutionDriverRuntime ExecutionFinish RootRun
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

def advanceRootState {K : Type} (before : RootDrainState K) (stage : Stage)
    (roots : Roots) (workspace : RowWorkspace) (meter : WorkMeter) : RootDrainState K :=
  ⟨{ before.execution with state := .Running stage, roots }, workspace, meter⟩

/-- Exact consecutive root-body successes give two original driver calls
with the source counters, state and workspace continuation. -/
def ActualNativeRootPairChunk : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (before : RootDrainState K) (input : RowInput) (first second next : Stage)
    (middleRoots finalRoots : Roots) (middleWorkspace finalWorkspace : RowWorkspace)
    (middleMeter finalMeter : WorkMeter),
    before.execution.state = .Running first → before.execution.degree_probe = none →
    rootStage first = true → rootStage second = true →
    Roots.run nativeCalls nativeDivRem RootSetup.gf64Dictionary kernels before.execution.roots
      first before.workspace before.meter = .ok (.Ok (.Ok second), middleRoots, middleWorkspace, id, middleMeter) →
    Roots.run nativeCalls nativeDivRem RootSetup.gf64Dictionary kernels middleRoots
      second middleWorkspace middleMeter = .ok (.Ok (.Ok next), finalRoots, finalWorkspace, id, finalMeter) →
    let middle := advanceRootState before second middleRoots middleWorkspace middleMeter
    let after := advanceRootState middle next finalRoots finalWorkspace finalMeter
    SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input 2 before after id

theorem native_root_pair_chunk : ActualNativeRootPairChunk := by
  intro canonicalize K kernels before input first second next middleRoots finalRoots middleWorkspace
    finalWorkspace middleMeter finalMeter running noProbe firstRoot secondRoot firstRan secondRan middle after
  have middleState : middle.execution.state = .Running second := rfl
  have middleProbe : middle.execution.degree_probe = none := noProbe
  have initial := native_root_driver_return canonicalize kernels before.execution first input before.workspace
    before.meter middleMeter (.Ok (.Ok second)) middleRoots middleWorkspace id running noProbe firstRoot firstRan
  have final := native_root_driver_return canonicalize kernels middle.execution second input middleWorkspace
    middleMeter finalMeter (.Ok (.Ok next)) finalRoots finalWorkspace id middleState middleProbe secondRoot secondRan
  refine SuccessfulChunk.step before middle after first (progress first { before.execution with roots := middleRoots })
    id id 1 running initial ?_
  exact SuccessfulChunk.step middle after after second (progress second { middle.execution with roots := finalRoots })
    id id 0 middleState final (.empty after)

#print axioms native_root_pair_chunk

end BulksketchBridge.ExecutionDriver
