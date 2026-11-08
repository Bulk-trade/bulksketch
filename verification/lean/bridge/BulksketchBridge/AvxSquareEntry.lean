import Arithmetic.AvxSquareEntryGenerated
import BulksketchBridge.AvxSquareAlgebra

namespace BulksketchBridge.AvxSquare

open Aeneas.Std Aeneas.Std.AvxSquareRuntime
open DenseReducerAlgebra
open bulksketch.backend.x86_vpclmul512
open scoped BulksketchBridge.DenseMulReductionSpec

abbrev originalSelector :=
  @Vpclmul512.Insts.BulksketchBackendContractBulkKernels.square_mod

/-- Exact native dispatch. Non-64-bit fields return false and preserve
both slices; GF64 calls the proved free accelerated body. -/
def ActualAvxSquareDispatch : Prop :=
  ∀ (loadModel : Load) (storeModel : Store) {F : Type}
    (field : bulksketch.field.BinaryField F) (bits : U32),
    field.BITS = .ok bits →
    ∀ (input table dst : Slice U64) (scratch : Slice Raw),
      Vpclmul512.Insts.BulksketchBackendContractBulkKernels.square_mod
        loadModel storeModel field input table dst scratch =
        if bits = 64#u32 then
          (do
            let (output, updated) ← square_mod loadModel storeModel input table dst scratch
            .ok (true, output, updated))
        else .ok (false, dst, scratch)

theorem square_mod_entry_refines : ActualAvxSquareDispatch := by
  intro loadModel storeModel F field bits read input table dst scratch
  by_cases is64 : bits = 64#u32
  · simp only [Vpclmul512.Insts.BulksketchBackendContractBulkKernels.square_mod,
      read, bind_ok, is64, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true]
  · have differs : (bits != 64#u32) = true := by simp [is64]
    simp only [Vpclmul512.Insts.BulksketchBackendContractBulkKernels.square_mod,
      read, bind_ok, differs, ite_true, is64, ite_false]

/-- Installing the original GF64 selector as the kernel callback
discharges Dense's accelerated remainder/frame premise. -/
theorem backend_law_of_original_selector {K : Type}
    (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (loadModel : Load) (storeModel : Store) (loadLaw : LoadLaw loadModel) (storeLaw : StoreLaw storeModel)
    (modulus table : Slice U64) (degree : Nat)
    (shape : modulus.length = degree + 1) (monic : modulus[degree]! = 1#u64)
    (valid : CorrectTable modulus table degree)
    (installed : ∀ (input dst : Slice U64) (scratch : Slice Raw),
      kernels.square_mod input table dst scratch =
        originalSelector loadModel storeModel bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
          input table dst scratch) :
    DenseReducerSquare.BackendSquareLaw kernels modulus table degree := by
  apply backend_law_of_dispatch kernels loadModel storeModel loadLaw storeLaw modulus table degree
    shape monic valid
  intro input dst scratch
  have read : (bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField).BITS = .ok 64#u32 := by
    simp [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS]
  rw [installed]
  change Vpclmul512.Insts.BulksketchBackendContractBulkKernels.square_mod
    loadModel storeModel bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input table dst scratch = _
  rw [square_mod_entry_refines loadModel storeModel
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField 64#u32 read]
  simp only [ite_true]

end BulksketchBridge.AvxSquare
