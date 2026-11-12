import Arithmetic.AvxLinearEntryGenerated
import BulksketchBridge.AvxMultiplyLinear

namespace BulksketchBridge.AvxMultiplyLinear

open Aeneas.Std AvxSquareRuntime AvxSquare
open bulksketch.backend.contract bulksketch.backend.portable
open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
  (multiply_linear)

/-- The original backend entry selects the proved AVX coefficient update
at the 64-bit field width. Other widths call the original default using
the supplied Portable dictionary. -/
def ActualNativeAvxLinearEntry : Prop :=
  ∀ (loadModel : Load) (storeModel : Store),
    LoadLaw loadModel → StoreLaw storeModel →
    ∀ (portableModel : {F : Type} → bulksketch.field.BinaryField F → BulkKernels Portable F)
      {F : Type} (field : bulksketch.field.BinaryField F) (bits : U32)
      (words : Slice U64) (root : U64),
    field.BITS = .ok bits →
    multiply_linear loadModel storeModel portableModel field words root =
      if bits = 64#u32 then .ok (RebuiltLfsr.linearStep words root)
      else BulkKernels.multiply_linear.default (portableModel field) words root

theorem native_avx_linear_entry : ActualNativeAvxLinearEntry := by
  intro loadModel storeModel loadLaw storeLaw portableModel F field bits words root bitWidth
  by_cases width : bits = 64#u32
  · rw [width] at bitWidth
    simp only [multiply_linear, bitWidth, bind_ok, bne_self_eq_false, Bool.false_eq_true, ite_false, width, ite_true]
    exact multiply_linear_refines loadModel storeModel loadLaw storeLaw words root
  · have other : (bits != 64#u32) = true := bne_iff_ne.mpr width
    simp only [multiply_linear, bitWidth, bind_ok, other, ite_true, width, ite_false]

#print axioms native_avx_linear_entry

end BulksketchBridge.AvxMultiplyLinear
