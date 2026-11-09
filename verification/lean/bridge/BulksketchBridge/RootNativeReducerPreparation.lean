import BulksketchBridge.RootReborrow
import BulksketchBridge.RootPendingFactors
import BulksketchBridge.NativeRootRun
import BulksketchBridge.DenseReducerTableAlgebra

namespace BulksketchBridge.RootRun

open Aeneas.Std DenseReducerTable DenseReducerAlgebra DenseCoefficient RebuiltLfsr BmEntry
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096

private theorem fill_table_width (modulus : Slice U64) (degree : Nat) (table current : Slice U64)
    (row count : Nat) :
    (fillRows modulus degree table current row count).1.length = table.length := by
  induction count generalizing table current row with
  | zero => rfl
  | succ count ih =>
    simp only [fillRows, ih, Slice.setSlice!_length]

/-- The original paid reducer stage writes the correct native table,
preserves the factor and work width, and reborrows the exact returned
windows at the following stage. -/
def ActualNativeReducerPreparation : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter)
    (capacity budget : Nat),
    BudgetBuffers workspace capacity budget → 3 ≤ roots.degree.val → roots.degree.val ≤ budget →
    TimesXMod.ExactScaleXor kernels →
    bulksketch.decode.roots.charge meter (.Table roots.degree) = .ok (.Ok (), paid) →
    let before := buffersFor roots workspace
    before.modulus[roots.degree.val]! = 1#u64 →
    ∃ table work,
      let updated := { before with table, work }
      let written := rebuild workspace roots updated
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .ReducerPreparation workspace meter =
        .ok (.Ok (.Ok (tableStage roots)), roots, written, id, paid) ∧
      buffersFor roots written = updated ∧
      CorrectTable before.modulus table roots.degree.val ∧
      workspaceLengths written = workspaceLengths workspace ∧
      activeFactor roots written = activeFactor roots workspace

theorem native_reducer_preparation : ActualNativeReducerPreparation := by
  intro K kernels roots workspace meter paid capacity budget sized degreeMin degreeBound scale charged before monic
  obtain ⟨ready, modWidth, traceWidth, gcdWidth, workRoom, _⟩ :=
    gcd_buffers_of_budget roots workspace capacity budget sized (by omega) degreeBound
  change before.modulus.length = roots.degree.val + 1 at modWidth
  change before.trace.length = roots.degree.val at traceWidth
  change before.gcd.length = roots.degree.val + 1 at gcdWidth
  change 4 * (roots.degree.val + 2) ≤ before.work.length at workRoom
  have tableWidth : before.table.length = RootSetup.tableCount roots.degree.val := by
    change (prefixSlice workspace.square_table (RootSetup.tableCount roots.degree.val)).length = _
    rw [prefix_length, Nat.min_eq_left ready.2]
  have deg : before.modulus.length - 1 = roots.degree.val := by omega
  have minimum : 4 ≤ before.modulus.length := by omega
  have leading : before.modulus[before.modulus.length - 1]! = 1#u64 := by rwa [deg]
  have room : (before.modulus.length - 1) * ((before.modulus.length - 1) / 2) ≤ before.table.length := by
    rw [deg, tableWidth, RootSetup.tableCount]
  have scratch : 4 * before.modulus.length ≤ before.work.length := by omega
  let result := expectedTable before.modulus before.table before.work
  have native := prepare_square_table_refines kernels scale before.modulus before.table before.work minimum leading room scratch
  have sound := expected_table_correct kernels scale before.modulus before.table before.work minimum leading room
  rw [deg] at sound
  let updated := { before with table := result.1, work := result.2 }
  let written := rebuild workspace roots updated
  have next : buffersFor roots written = updated := by
    apply reborrow_factor_work roots workspace updated ready
    · exact modWidth
    · exact traceWidth
    · exact gcdWidth
    · change result.2.length = _
      have unchanged : result.2.length = before.work.length := Slice.setSlice!_length ..
      rw [unchanged]
      change (tail (tail (tail workspace.polynomials (roots.degree.val + 1)) roots.degree.val)
        (roots.degree.val + 1)).length = _
      simp only [tail_length]
    · change result.1.length = _
      have unchanged : result.1.length = before.table.length := fill_table_width ..
      rw [unchanged, tableWidth]
  refine ⟨result.1, result.2, ?_, next, sound, ?_, ?_⟩
  · rw [original_root_run_refines kernels roots .ReducerPreparation workspace meter ready]
    unfold expected reducer
    rw [charged, Aeneas.Std.bind_ok]
    dsimp! only
    rw [native]
    simp only [Aeneas.Std.bind_ok]
    rfl
  · simp only [workspaceLengths, rebuild, RootSetup.restoreWork, splitBack_length, restore_length]
    rfl
  · change SliceKernels.slicePolynomial (buffersFor roots written).modulus =
      SliceKernels.slicePolynomial before.modulus
    rw [next]

#print axioms native_reducer_preparation

end BulksketchBridge.RootRun
