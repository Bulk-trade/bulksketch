import BulksketchBridge.CandidateEntry
import BulksketchBridge.AffineEnumerationHorner

namespace BulksketchBridge.CandidateOuter

open Aeneas.Std Algebra.Gf64
open bulksketch.backend.contract

/-- The same original backend Horner theorem used by affine enumeration
    supplies the exact candidate scan words. -/
theorem candidate_horner_of_polynomial {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (law : AffineEnumerate.HornerLaw kernels) : HornerLaw kernels := by
  intro coefficients points values aligned
  obtain ⟨written, called, width, fieldValues⟩ := law coefficients points values aligned.symm
  have expectedLength : written.length = (evaluated coefficients points).length := by
    rw [evaluated_length, width, aligned]
  have exactWords : written = evaluated coefficients points := by
    apply Slice.ext_getElem expectedLength
    intro index inWritten inExpected
    have active : index < points.length := by rwa [width, aligned] at inWritten
    have expectedWord : (evaluated coefficients points)[index]! =
        PortableHornerChallenges.evalWord coefficients.val points[index]! := by
      simp only [evaluated, Slice.getElem!_Nat_eq, Slice.from_val]
      rw [← List.Inhabited_getElem_eq_getElem! _ _ (by simpa only [List.length_map] using active),
        List.getElem_map, List.Inhabited_getElem_eq_getElem! _ _ active]
    rw [Slice.Inhabited_getElem_eq_getElem! _ _ inWritten, Slice.Inhabited_getElem_eq_getElem! _ _ inExpected]
    apply U64.bv_eq_imp_eq
    apply toField_injective
    rw [fieldValues index active, expectedWord, PortableHorner.horner_word_evaluates]
  rw [called, exactWords]

#print axioms candidate_horner_of_polynomial

end BulksketchBridge.CandidateOuter
