import BulksketchBridge.RootRun
import BulksketchBridge.AffineMultipleWrapper
import BulksketchBridge.DenseDivRemComposition

namespace BulksketchBridge.RootRun

open Aeneas.Std
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

abbrev nativeCalls : Calls :=
  ⟨⟨bulksketch.decode.affine.multiple RootTrace.nativeSquare⟩⟩

abbrev nativeDivRem : DivRem :=
  bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into

/-- Specialize the exact dispatcher to the original affine multiple and
    original Dense division. The admitted row and stage contracts remain
    the same as in the general dispatcher theorem. -/
def ActualNativeRootRun : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (stage : Stage) (workspace : RowWorkspace) (meter : WorkMeter),
    Ready nativeDivRem kernels roots stage workspace meter →
    Roots.run nativeCalls nativeDivRem dictionary kernels roots stage workspace meter =
      expected nativeCalls nativeDivRem kernels roots stage workspace meter

theorem original_root_run_refines : ActualNativeRootRun := by
  intro K kernels roots stage workspace meter admitted
  exact run_refines nativeCalls nativeDivRem kernels roots stage workspace meter admitted

end BulksketchBridge.RootRun
