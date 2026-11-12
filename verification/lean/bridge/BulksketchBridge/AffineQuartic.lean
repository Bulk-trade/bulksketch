import BulksketchBridge.AffineQuarticFibers
import BulksketchBridge.AffineQuarticMin
import BulksketchBridge.CertificatePolynomial

namespace BulksketchBridge.AffineQuartic

open Aeneas Aeneas.Std Algebra.Gf64 bulksketch.backend.contract
open BulksketchBridge.AffineQuarticMin

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

private theorem slice_lengths (b c : U64) (kernel : Array U64 3#usize) :
    (Array.to_slice kernel).length + 1 ≤ Usize.max ∧ (factorWords b c).length ≤ scratchWords.length := by
  constructor
  · have size := Slice.length_ineq (factorWords b c)
    simpa [factorWords, Array.to_slice, Slice.length] using size
  · simp [factorWords, scratchWords, Array.to_slice, Slice.length]

private theorem other_kernel_word (kernel : Array U64 3#usize)
    (valid : Certificate.ValidRoots (Array.to_slice kernel)) (u : U64) :
    ∃ r ∈ kernel.val, r ≠ 0#u64 ∧ r ≠ u := by
  let words := Array.to_slice kernel
  have length : words.length = 3 := by simp [words, Array.to_slice, Slice.length]
  have first := valid 0 (by rw [length]; decide)
  have second := valid 1 (by rw [length]; decide)
  have different := second.2 0 (by decide)
  have member (i : Nat) (bounded : i < words.length) : words[i]! ∈ kernel.val := by
    rw [Slice.getElem!_Nat_eq]
    have inList : i < words.val.length := bounded
    rw [← List.Inhabited_getElem_eq_getElem! words.val i inList]
    simpa only [words, Array.val_to_slice] using (List.getElem_mem inList)
  by_cases firstIsU : words[0]! = u
  · exact ⟨words[1]!, member 1 (by omega), second.1, fun equal => different (firstIsU.trans equal.symm)⟩
  · exact ⟨words[0]!, member 0 (by omega), first.1, firstIsU⟩

private theorem kernel_facts (b c : U64) (kernel : Array U64 3#usize)
    (nonzeroC : c ≠ 0#u64) (valid : Certificate.ValidRoots (Array.to_slice kernel))
    (root : ∀ word ∈ kernel.val,
      toField word.bv ^ 3 + toField b.bv * toField word.bv + toField c.bv = 0) :
    let u := kernelMinimum kernel
    let v := b ^^^ squareWord u
    toField u.bv ≠ 0 ∧ toField v.bv ≠ 0 ∧
      toField b.bv = toField v.bv + toField u.bv ^ 2 ∧
      toField u.bv * toField v.bv = toField c.bv ∧
      ∃ r, quadratic (toField u.bv) r = toField v.bv := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  let u := kernelMinimum kernel
  let v := b ^^^ squareWord u
  have vMeaning : toField v.bv = toField b.bv + toField u.bv ^ 2 := by
    simp only [v, toField_xorWord]
    exact congrArg (toField b.bv + ·) (toField_square _)
  have coefB : toField b.bv = toField v.bv + toField u.bv ^ 2 := by
    rw [vMeaning, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have product : toField u.bv * toField v.bv = toField c.bv := by
    rw [vMeaning]
    exact factor_from_kernel_root _ _ _ (root u (kernelMinimum_mem kernel))
  have nonzero := mul_ne_zero_iff.mp (product ▸ nonzero_field c nonzeroC)
  obtain ⟨r, rMem, rNonzero, rDiff⟩ := other_kernel_word kernel valid u
  refine ⟨nonzero.1, nonzero.2, coefB, product, toField r.bv, ?_⟩
  apply nontrivial_kernel_fiber _ _ _
  · rw [← coefB, product]
    exact root r rMem
  · exact nonzero_field r rNonzero
  · intro same
    exact rDiff (U64.bv_eq_imp_eq _ _ (toField_injective same))

private theorem certified_iff {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (b c : U64) (kernel : Array U64 3#usize) (accepted : Bool) (scratch : Slice U64)
    (cubicCall : bulksketch.decode.deg34.cubic fieldDictionary kernels 0#u64 b c = .ok (some kernel))
    (certCall : bulksketch.decode.deg34.certificate fieldDictionary kernels (factorWords b c)
      (Array.to_slice kernel) scratchWords = .ok (accepted, scratch)) :
    CertifiedKernel kernels b c ↔ accepted = true := by
  constructor
  · rintro ⟨selected, updated, selectedCall, checked⟩
    rw [cubicCall] at selectedCall
    have same := Option.some.inj (Result.ok_injective selectedCall)
    subst selected
    rw [certCall] at checked
    exact congrArg Prod.fst (Result.ok_injective checked)
  · intro yes
    exact ⟨kernel, scratch, cubicCall, yes ▸ certCall⟩

private theorem certified_normal {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (b c d : U64) (kernel : Array U64 3#usize) (scratch : Slice U64)
    (arithmetic : Cubic.CorrectArithmetic kernels) (nonzeroC : c ≠ 0#u64)
    (cubicCall : bulksketch.decode.deg34.cubic fieldDictionary kernels 0#u64 b c = .ok (some kernel))
    (certCall : bulksketch.decode.deg34.certificate fieldDictionary kernels (factorWords b c)
      (Array.to_slice kernel) scratchWords = .ok (true, scratch))
    (nonzeroU : kernelMinimum kernel ≠ 0#u64)
    (nonzeroV : b ^^^ squareWord (kernelMinimum kernel) ≠ 0#u64)
    (product : mulWord (kernelMinimum kernel) (b ^^^ squareWord (kernelMinimum kernel)) = c) :
    bulksketch.decode.deg34.affine_quartic fieldDictionary kernels b c d =
      .ok (fiberChoices (kernelMinimum kernel) (b ^^^ squareWord (kernelMinimum kernel)) c d) := by
  have mulNormal (left right : U64) : kernels.ArithmeticInst.mul left right = .ok (mulWord left right) :=
    (arithmetic.1.1 left right).trans (native_mul_word left right)
  have squareNormal (word : U64) : kernels.ArithmeticInst.square word = .ok (squareWord word) :=
    (arithmetic.1.2.1 word).trans (Square.square_refines word)
  have quadNormal := Cubic.quadratic_refines kernels arithmetic.1.2.1 arithmetic.2.2
  have invNormal : kernels.ArithmeticInst.inverse c = Result.ok (some (inverseWord c)) :=
    Cubic.inverse_normal kernels arithmetic c nonzeroC
  have minNormal := kernel_minimum_refines kernel
  let u := kernelMinimum kernel
  let v := b ^^^ squareWord u
  change bulksketch.decode.deg34.affine_quartic fieldDictionary kernels b c d =
    .ok (fiberChoices u v c d)
  change u ≠ 0#u64 at nonzeroU
  change v ≠ 0#u64 at nonzeroV
  change mulWord u v = c at product
  change _ = Result.ok (some u) at minNormal
  have valueV : b ^^^ squareWord u = v := rfl
  simp only [factorWords, scratchWords] at certCall
  unfold bulksketch.decode.deg34.affine_quartic fiberChoices
  simp only [nonzeroC, ite_false, cubicCall, bind_ok, lift, Array.to_slice_mut,
    bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  dsimp! only
  simp only [certCall, bind_ok]
  dsimp! only
  simp only [eq_self, ite_true, core.slice.Slice.iter, bind_ok, minNormal, core.option.Option.expect, Result.ofOption,
    squareNormal, valueV, nonzeroU, nonzeroV, ite_false, mulNormal, product,
    bne_self_eq_false, Bool.false_eq_true, invNormal, quadNormal, scaledTarget]
  cases outer : MapsQuadratic.expectedSolution (scaledTarget u (inverseWord c) d) with
  | none =>
    simp only [scaledTarget] at outer
    simp [outer,
      bulksketch.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
  | some outerWord =>
    simp only [scaledTarget] at outer
    simp only [outer,
      Option.bind_eq_bind, Option.bind_some]
    cases first : MapsQuadratic.expectedSolution
        (scaledTarget v (inverseWord c) (mulWord v outerWord)) with
    | none =>
      simp only [scaledTarget] at first
      simp [first,
        bulksketch.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
    | some firstWord =>
      simp only [scaledTarget] at first
      simp only [first, Option.bind_some]
      cases second : MapsQuadratic.expectedSolution
          (scaledTarget v (inverseWord c) (mulWord v outerWord ^^^ v)) <;>
        simp only [scaledTarget] at second <;>
        simp [second,
          bulksketch.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]

theorem affine_quartic_refines : ActualAffineQuarticRefines := by
  intro K kernels b c d arithmetic
  by_cases cZero : c = 0#u64
  · refine ⟨none, ?_, ?_, ?_⟩
    · simp [bulksketch.decode.deg34.affine_quartic, cZero]
    · simp
    · simp [cZero]
  · obtain ⟨cubicOutput, cubicCall, cubicSound⟩ := Cubic.cubic_refines kernels 0#u64 b c arithmetic
    cases cubicOutput with
    | none =>
      refine ⟨none, ?_, ?_, ?_⟩
      · simp [bulksketch.decode.deg34.affine_quartic, cZero, cubicCall,
          bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          bulksketch.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
      · simp
      · simp [CertifiedKernel, cubicCall]
    | some kernel =>
      obtain ⟨bounded, room⟩ := slice_lengths b c kernel
      have certCall := Certificate.certificate_refines kernels arithmetic.1.1
        (factorWords b c) (Array.to_slice kernel) scratchWords bounded (fun _ _ => room)
      cases certResult : Certificate.expected (factorWords b c) (Array.to_slice kernel) scratchWords with
      | mk accepted scratch =>
        rw [certResult] at certCall
        have certIff := certified_iff kernels b c kernel accepted scratch cubicCall certCall
        cases accepted with
        | false =>
          refine ⟨none, ?_, ?_, ?_⟩
          · simp only [factorWords, scratchWords] at certCall
            simp [bulksketch.decode.deg34.affine_quartic, cZero, cubicCall, certCall, lift, Array.to_slice_mut,
              bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
          · simp
          · simp [certIff]
        | true =>
          have valid := ((Certificate.certificate_accepts_root_polynomial kernels arithmetic.1.1
            (factorWords b c) (Array.to_slice kernel) scratchWords bounded (fun _ _ => room)).mp
            ⟨scratch, certCall⟩).2.1
          have root word (mem : word ∈ kernel.val) :
              toField word.bv ^ 3 + toField b.bv * toField word.bv + toField c.bv = 0 := by
            simpa only [show toField (0#u64).bv = 0 from toField_zero, zero_mul, add_zero] using
              cubicSound kernel rfl word mem
          obtain ⟨uNZ, vNZ, coefB, product, fiber⟩ := kernel_facts b c kernel cZero valid root
          have productWord : mulWord (kernelMinimum kernel) (b ^^^ squareWord (kernelMinimum kernel)) = c := by
            apply U64.bv_eq_imp_eq
            apply toField_injective
            exact (toField_mul _ _).trans product
          have normal := certified_normal kernels b c d kernel scratch arithmetic cZero cubicCall certCall
            (nonzero_word _ uNZ) (nonzero_word _ vNZ) productWord
          have meaning := fiber_choices_refine b c d _ _ uNZ vNZ coefB product fiber
          exact ⟨_, normal, meaning.1, by simpa [cZero, certIff] using meaning.2⟩

end BulksketchBridge.AffineQuartic
