import BulksketchBridge.AffineEnumerationBatch
import BulksketchBridge.HornerPolynomial
import BulksketchBridge.X86PclmulHorner
import BulksketchBridge.AvxHorner

namespace BulksketchBridge.AffineEnumerate

open Aeneas.Std SliceKernels Algebra.Gf64
open bulksketch.backend.contract

/-- Install the original Portable method in the enumerator's Horner slot. -/
theorem horner_law_of_portable {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (installed : kernels.horner_many =
      bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.horner_many
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField) : HornerLaw kernels := by
  intro polynomial points values aligned
  obtain ⟨evaluated, ran, width, words⟩ :=
    PortableHorner.horner_many_polynomial_refines polynomial points values aligned.symm
  exact ⟨evaluated, installed ▸ ran, width.trans aligned, words⟩

theorem pclmul_horner_polynomial (polynomial points values : Slice U64)
    (aligned : points.length = values.length) :
    ∃ evaluated,
      bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.horner_many
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField polynomial points values = Result.ok evaluated ∧
      evaluated.length = values.length ∧
      ∀ i < points.length,
        toField evaluated[i]!.bv = (slicePolynomial polynomial).eval (toField points[i]!.bv) := by
  let evaluated := X86PclmulHornerChallenges.expectedOutput polynomial points values
  have ran := X86PclmulHorner.horner_entry_refines polynomial points values
  rw [ite_eq_left aligned.symm] at ran
  refine ⟨evaluated, ran, ?_, ?_⟩
  · unfold evaluated X86PclmulHornerChallenges.expectedOutput
    split <;> simp [Slice.length]
  · intro i active
    have bound : i < values.length := by rwa [← aligned]
    have word : evaluated[i]! = PortableHornerChallenges.evalWord polynomial.val points[i]! := by
      unfold evaluated X86PclmulHornerChallenges.expectedOutput PortableHornerChallenges.evalWord
      cases reversed : polynomial.val.reverse with
      | nil => simp only [Slice.getElem!_Nat_eq, Slice.from_val, List.getElem!_replicate, bound]
      | cons leading rest =>
        rw [MutableZip.mapPrefixFrom_word _ _ _ _ _ bound,
          ite_eq_left ⟨Nat.zero_le _, active⟩]
    rw [word]
    exact PortableHorner.horner_word_evaluates polynomial points[i]!

/-- Install the original PCLMUL selector, including its Portable fallback. -/
theorem horner_law_of_pclmul {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (installed : kernels.horner_many =
      bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.horner_many
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField) : HornerLaw kernels := by
  intro polynomial points values aligned
  rw [installed]
  exact pclmul_horner_polynomial polynomial points values aligned

open Aeneas.Std.AvxSquareRuntime AvxSquare in
/-- Install the original AVX-512 method under its masked slice contracts. -/
theorem horner_law_of_avx {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (loadModel : Load) (storeModel : Store)
    (loadLaw : LoadLaw loadModel) (storeLaw : StoreLaw storeModel)
    (installed : kernels.horner_many =
      bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.horner_many
        loadModel storeModel bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField) : HornerLaw kernels := by
  intro polynomial points values aligned
  rw [installed]
  exact AvxHorner.trait_polynomial_refines loadModel storeModel loadLaw storeLaw polynomial points values aligned.symm

end BulksketchBridge.AffineEnumerate
