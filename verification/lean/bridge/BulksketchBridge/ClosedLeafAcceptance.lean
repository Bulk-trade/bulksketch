import BulksketchBridge.ClosedLeafAcceptanceSpec
import BulksketchBridge.ClosedLeaf
import BulksketchBridge.ClosedLeafAdvance

namespace BulksketchBridge.ClosedLeaf

open Aeneas Aeneas.Std Aeneas.Std.WP
open bulksketch.types bulksketch.decode.roots bulksketch.decode.scratch bulksketch.backend.contract

theorem certificate_meaning : ActualClosedLeafCertificateMeaning := by
  intro K kernels roots workspace arithmetic admitted
  have room := admitted.verificationRoom rfl
  have count := admitted.candidateCount rfl
  have degree := degree_values roots admitted.degree
  have factorLen := factor_length roots workspace degree (by omega)
  have candidateLen : (candidateWords roots workspace).length = roots.solved_count.val := by
    rw [candidateWords, region_length _ _ _ (by omega)]
    omega
  have productLen : (productWords workspace).length = 5 := region_length _ _ _ room
  have maxLen := Slice.length_ineq workspace.polynomials
  change workspace.polynomials.length ≤ Usize.max at maxLen
  have checked := Certificate.certificate_refines kernels arithmetic.1.1 (factorWords roots workspace)
    (candidateWords roots workspace) (productWords workspace) (by omega) (by intros; omega)
  have meaning := Certificate.certificate_accepts_root_polynomial kernels arithmetic.1.1
    (factorWords roots workspace) (candidateWords roots workspace) (productWords workspace)
    (by omega) (by intros; omega)
  rw [checked] at meaning
  have accepted : ((certificateResult roots workspace).1 = true) ↔
      ∃ out, Result.ok (certificateResult roots workspace) = Result.ok (true, out) := by
    constructor
    · intro yes
      exact ⟨_, congrArg Result.ok (Prod.ext yes rfl)⟩
    · rintro ⟨out, normal⟩
      exact congrArg Prod.fst (Result.ok_injective normal)
  exact accepted.trans (by simpa only [certificateResult, candidateLen, factorLen, Nat.add_right_cancel_iff] using meaning)

theorem accepted_advance : ActualClosedLeafAcceptedAdvance := by
  intro K kernels roots workspace meter finalMeter product arithmetic admitted charged cert
  have rootRoom := admitted.rootRoom rfl (by rw [cert])
  obtain ⟨count, addCount, countVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := roots.count) (y := roots.degree)
      (by have maxRoots := Slice.length_ineq workspace.roots
          change workspace.roots.length ≤ Usize.max at maxRoots
          omega))
  let updated := { roots with count }
  let scratch := acceptedWorkspace roots workspace product
  have normal := closed_leaf_refines kernels roots .FactorVerification workspace meter arithmetic admitted
  simp only [expected, charged, verifying, ite_true, verificationFrame, cert, addCount, bind_ok, eq_self] at normal
  refine ⟨count, countVal, ?_, ?_⟩
  · intro empty
    have advance := ClosedLeafAdvance.advance_empty_refines updated scratch empty
    rw [normal, advance]
    simp [normalReturn, updated, scratch]
  · intro frame bounds
    have advance := ClosedLeafAdvance.advance_pop_refines updated scratch frame bounds
    rw [normal, advance]
    simp [normalReturn, updated, scratch]

end BulksketchBridge.ClosedLeaf
