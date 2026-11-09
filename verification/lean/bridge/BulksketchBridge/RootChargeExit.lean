import BulksketchBridge.NativeTraversalDriver

namespace BulksketchBridge.RootRun

open Aeneas.Std DenseCoefficient BmEntry RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch
open bulksketch.decode.work bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem splitBack_original (words : Slice U64) (count : Nat) :
    splitBack words count (prefixSlice words count, tail words count) = words := by
  unfold splitBack
  split
  · apply Slice.ext
    simp only [prefixSlice, tail, Slice.from_val, List.take_append_drop]
  · rfl

private theorem restorePrefix_original (words : Slice U64) (count : Nat) :
    restorePrefix words (prefixSlice words count) = words := by
  apply Slice.ext
  simp only [restorePrefix, prefixSlice, Slice.from_val, List.setSlice!, List.take_zero,
    List.nil_append, Nat.sub_zero, Nat.zero_add]
  rw [Nat.min_eq_left (by simp : (List.take count words.val).length ≤ words.val.length), List.take_length]
  conv_rhs => rw [← List.take_append_drop (List.take count words.val).length words.val]
  rw [List.length_take, ← List.take_take, List.take_length]

theorem rebuild_original (roots : Roots) (workspace : RowWorkspace) :
    rebuild workspace roots (buffersFor roots workspace) = workspace := by
  simp only [rebuild, buffersFor, RootSetup.workRegions, RootSetup.restoreWork,
    splitBack_original, restorePrefix_original]

def firstFactorCharge (roots : Roots) : Stage → Option Charge
  | .ReducerPreparation => some (.Table roots.degree)
  | .AffineSplit => some (.AffineSplit roots.degree roots.affine_rank)
  | .Trace => some (.Trace roots.degree)
  | .Gcd => some (.Gcd roots.degree)
  | .FactorDivision => some (.Divide roots.degree)
  | _ => none

/-- A first charge error exits the original factor-work stage before
running its arithmetic callee and restores the exact workspace. -/
def ActualNativeFactorChargeExit : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (stage : Stage) (operation : Charge) (workspace : RowWorkspace)
    (meter finalMeter : WorkMeter) (failure : DecodeError),
    factorReady roots workspace → firstFactorCharge roots stage = some operation →
    charge meter operation = .ok (.Err failure, finalMeter) →
    Roots.run nativeCalls nativeDivRem dictionary kernels roots stage workspace meter =
      .ok (.Err failure, roots, workspace, id, finalMeter)

theorem native_factor_charge_exit : ActualNativeFactorChargeExit := by
  intro K kernels roots stage operation workspace meter finalMeter failure ready selected charged
  have original : Ready nativeDivRem kernels roots stage workspace meter := by
    cases stage <;> simp only [firstFactorCharge, Option.some.injEq] at selected
    all_goals first | subst operation | cases selected
    all_goals first | exact ready | exact ⟨ready, fun paid success => by
      rw [charged] at success
      have different : (core.result.Result.Err failure, finalMeter) =
          (core.result.Result.Ok (), paid) := Result.ok_injective success
      have impossible : (core.result.Result.Err failure : core.result.Result Unit DecodeError) = .Ok () :=
        congrArg (fun value : core.result.Result Unit DecodeError × WorkMeter => value.1) different
      cases impossible⟩
  rw [original_root_run_refines kernels roots stage workspace meter original]
  cases stage <;> simp only [firstFactorCharge, Option.some.injEq] at selected
  all_goals first | subst operation | cases selected
  all_goals simp only [expected, reducer, affineSplit, gcdStage, charged, bind_ok, frame]
  all_goals try rw [RootTrace.trace_charge_failure _ _ _ _ _ _ _ charged]
  all_goals try rw [RootDivide.first_charge_failure _ _ _ _ _ _ _ _ _ _ charged]
  all_goals try simp only [RootDivide.unchanged, bind_ok]
  all_goals
    change Result.ok (core.result.Result.Err failure, roots,
      rebuild workspace roots (buffersFor roots workspace), id, finalMeter) = _
    rw [rebuild_original]

#print axioms native_factor_charge_exit

end BulksketchBridge.RootRun
