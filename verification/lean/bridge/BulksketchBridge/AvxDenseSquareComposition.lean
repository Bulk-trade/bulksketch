import BulksketchBridge.AvxSquareEntry
import BulksketchBridge.DenseReducerSquareAlgebra

namespace BulksketchBridge.AvxSquare

open Aeneas.Std Aeneas.Std.AvxSquareRuntime
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec
open bulksketch.backend.contract
open scoped BulksketchBridge.DenseMulReductionSpec

/-- The original accelerated selector discharges the backend law of the
original Dense modular square. Its typed installation and masked memory
premises keep dispatch correspondence and physical memory explicit. -/
def ActualAvxDenseModularSquare : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (loadModel : Load) (storeModel : Store),
    LoadLaw loadModel → StoreLaw storeModel →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    ∀ (modulus table : Slice U64) (degree : Nat),
      4 ≤ modulus.length → modulus.length = degree + 1 → modulus[degree]! = 1#u64 →
      table.length = degree * (degree / 2) → CorrectTable modulus table degree →
      (∀ (input dst : Slice U64) (scratch : Slice bulksketch.types.RawProduct),
        kernels.square_mod input table dst scratch =
          originalSelector loadModel storeModel bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
            input table dst scratch) →
      RootTrace.ModularSquareLaw bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into
        kernels modulus table degree

theorem avx_dense_modular_square : ActualAvxDenseModularSquare := by
  intro K kernels loadModel storeModel loadLaw storeLaw raw square reduce modulus table degree
    minimum shape monic tableLen valid installed
  exact native_modular_square kernels raw square reduce modulus table degree minimum shape monic tableLen valid
    (backend_law_of_original_selector kernels loadModel storeModel loadLaw storeLaw modulus table degree
      shape monic valid installed)

end BulksketchBridge.AvxSquare
