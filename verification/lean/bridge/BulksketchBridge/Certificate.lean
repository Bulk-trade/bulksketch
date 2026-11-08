import BulksketchBridge.CertificateSpec

namespace BulksketchBridge.Certificate

open Aeneas Aeneas.Std Aeneas.Std.WP RebuiltLfsr DenseCoefficient
open bulksketch.backend.contract bulksketch.decode.deg34

private theorem contains_exact (words : Slice U64) (word : U64) :
    core.slice.Slice.contains core.cmp.PartialEqU64 words word = Result.ok (decide (word ∈ words.val)) := by
  unfold core.slice.Slice.contains
  induction words.val with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.anyM_cons, liftFun2, core.cmp.impls.PartialEqU64.eq, ih, List.mem_cons]
    by_cases same : word = head <;> simp [same, pure, Bind.bind]

private theorem closure_exact {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Slice U64) (index : Usize) (bounded : index.val < roots.length) :
    certificate.closure.Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0U64Bool.call_mut
      fieldDictionary kernels roots (index, roots[index.val]!) =
      Result.ok (decide (invalidAt roots index.val), roots) := by
  unfold certificate.closure.Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0U64Bool.call_mut
  by_cases zero : roots[index.val]! = 0#u64
  · simp [zero, invalidAt]
  · have mask : roots[index.val]! &&& ~~~bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK = 0#u64 := by
      apply U64.bv_eq_imp_eq
      simp [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK, core.num.U64.MAX, U64.rMax]
    change (if roots[index.val]! = 0#u64 then Result.ok (true, roots) else _) = _
    rw [ite_eq_right zero]
    change (do
      let m ← Result.ok bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK
      let inv ← lift (~~~ m)
      let masked ← lift (roots[index.val]! &&& inv)
      if masked != 0#u64 then Result.ok (true, roots) else do
        let window ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U64) roots ⟨index⟩
        let found ← core.slice.Slice.contains core.cmp.PartialEqU64 window roots[index.val]!
        Result.ok (found, roots)) = _
    simp only [Bind.bind, bind_ok, lift, mask, bne_self_eq_false, Bool.false_eq_true, ite_false,
      Slice.index_SliceIndexRangeToUsizeSliceInst, shared_prefix_normal roots index (by omega), contains_exact,
      invalidAt, zero, false_or, prefixSlice, Slice.from_val]

private abbrev predicate {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) :=
  certificate.closure.Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0U64Bool fieldDictionary kernels

private abbrev rootsIterator := core.iter.traits.iterator.IteratorEnumerate
  (core.iter.traits.iterator.IteratorSliceIter U64)

private theorem any_exact {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Slice U64) (index : Usize) (count : Nat) (remaining : index.val + count = roots.length) :
    ∃ final : RootIterator,
      CertificateRuntime.any rootsIterator (predicate kernels) (⟨⟨roots, index.val⟩, index⟩ : RootIterator) roots =
        Result.ok (invalidFrom roots index.val count, final) := by
  induction count generalizing index with
  | zero =>
    obtain ⟨terminal, stop⟩ := root_done roots index (by omega)
    refine ⟨terminal, ?_⟩
    unfold CertificateRuntime.any loop
    dsimp only
    simp only [stop, bind_ok]
    dsimp! only
    simp only [bind_ok]
  | succ count ih =>
    have active : index.val < roots.length := by omega
    obtain ⟨next, read, advanced⟩ := root_next roots index active
    obtain ⟨final, normal⟩ := ih next (by omega)
    by_cases invalid : invalidAt roots index.val
    · refine ⟨⟨⟨roots, next.val⟩, next⟩, ?_⟩
      unfold CertificateRuntime.any loop
      dsimp only
      simp only [read, bind_ok]
      dsimp! only
      simp only [closure_exact kernels roots index active, invalid, decide_true, Bool.true_or, bind_ok]
      dsimp! only
      simp only [ite_true, bind_ok]
    · refine ⟨final, ?_⟩
      unfold CertificateRuntime.any loop
      dsimp only
      simp only [read, bind_ok]
      dsimp! only
      simp only [closure_exact kernels roots index active, invalid, decide_false, Bool.false_or, bind_ok]
      dsimp! only
      simp only [Bool.false_eq_true, ite_false, bind_ok]
      change CertificateRuntime.any rootsIterator (predicate kernels) (⟨⟨roots, next.val⟩, next⟩ : RootIterator) roots = _
      rw [normal, advanced]

private theorem equality_exact (left right : Slice U64) :
    CertificateRuntime.mutableSharedEq (bulksketch.Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU64)
      left right = Result.ok (decide (left = right)) := by
  change core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU64 left right = _
  obtain ⟨equal, normal, meaning⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU64 left right (by
      intro x y; simp [liftFun2, spec_ok]))
  rw [normal]
  congr 1
  cases equal <;> simp_all

/-- The exact native certificate wrapper uses the proved descending and outer
loops and the original short-circuit root validation closure. -/
theorem certificate_refines : ActualCertificateReturnsExactFrame := by
  intro K kernels mul factor roots scratch bounded room
  obtain ⟨size, plus, sizeVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := roots.len) (y := 1#usize) (by simpa using bounded))
  have sizeExact : size.val = roots.length + 1 := by simpa using sizeVal
  by_cases mismatch : roots.length + 1 ≠ factor.length
  · have different : (size != factor.len) = true := by
      have unequal : size ≠ factor.len := by intro equal; apply mismatch; rw [← sizeExact, equal]; rfl
      simpa using unequal
    simp only [certificate, plus, bind_ok, different, ite_true, expected, ite_eq_left (Or.inl mismatch)]
  · have lengths : roots.length + 1 = factor.length := of_not_not mismatch
    have same : size = factor.len := by scalar_tac
    obtain ⟨final, anyNormal⟩ := any_exact kernels roots 0#usize roots.length (by simp)
    have checkInitial : CertificateRuntime.any rootsIterator (predicate kernels)
        (⟨⟨roots, 0⟩, 0#usize⟩ : RootIterator) roots =
        Result.ok (invalidFrom roots 0 roots.length, final) := anyNormal
    by_cases invalid : invalidFrom roots 0 roots.length = true
    · rw [expected, ite_eq_left (Or.inr invalid)]
      simp only [certificate, plus, bind_ok, same, bne_self_eq_false, Bool.false_eq_true, ite_false,
        core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
        core.iter.traits.iterator.Iterator.enumerate.default, checkInitial, invalid]
      dsimp! only
      simp only [ite_true]
    · have valid : invalidFrom roots 0 roots.length = false := Bool.eq_false_iff.mpr invalid
      have fits := room lengths valid
      let window := prefixSlice scratch factor.length
      have prefixLen : window.length = factor.length := by simp [window, Nat.min_eq_left fits]
      have initBound : (0#usize).val < (zeroWords window).length := by
        rw [zero_length, prefixLen]; change 0 < factor.length; omega
      obtain ⟨initial, initNormal, initValue⟩ := RawMulTable.normal_of_spec _ _
        (Slice.update_spec (zeroWords window) 0#usize 1#u64 initBound)
      have initialized : initial = (zeroWords window).setAtNat 0 1#u64 := initValue
      have initialLen : initial.length = factor.length := by rw [initialized, Slice.setAtNat_length, zero_length, prefixLen]
      have outerNormal := outer_refines kernels mul roots initial 0#usize roots.length (by simp)
        (by rw [initialLen]; omega)
      have productExact : productFrom roots initial (0#usize).val roots.length = rebuiltProduct roots window := by
        rw [initialized]; rfl
      have outerInitial : certificate_loop0 fieldDictionary kernels
          (⟨⟨roots, 0⟩, 0#usize⟩ : RootIterator) initial = Result.ok (rebuiltProduct roots window) :=
        outerNormal.trans (congrArg Result.ok productExact)
      simp only [certificate, plus, bind_ok, same, bne_self_eq_false, Bool.false_eq_true, ite_false,
        core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
        core.iter.traits.iterator.Iterator.enumerate.default, checkInitial, valid,
        Slice.index_mut_SliceIndexRangeToUsizeSliceInst, prefix_normal scratch factor.len (by simpa using fits),
        fill_zero, equality_exact, expected, mismatch, false_or]
      dsimp! only
      simp only [Bool.false_eq_true, ite_false, Slice.len_val]
      change (do
        let initial ← Slice.update (zeroWords window) 0#usize 1#u64
        let built ← certificate_loop0 fieldDictionary kernels (⟨⟨roots, 0⟩, 0#usize⟩ : RootIterator) initial
        Result.ok (decide (built = factor), restorePrefix scratch built)) =
        Result.ok (decide (rebuiltProduct roots window = factor), restorePrefix scratch (rebuiltProduct roots window))
      simp only [initNormal, outerInitial, bind_ok]

/-- A false scan result excludes the zero and duplicate checks at every visited index. -/
theorem invalidFrom_false_iff (roots : Slice U64) (index count : Nat) :
    invalidFrom roots index count = false ↔ ∀ offset, offset < count → ¬ invalidAt roots (index + offset) := by
  induction count generalizing index with
  | zero => simp [invalidFrom]
  | succ count ih =>
    rw [invalidFrom, Bool.or_eq_false_iff, decide_eq_false_iff_not, ih]
    constructor
    · rintro ⟨first, rest⟩ offset bounded
      cases offset with
      | zero => simpa only [Nat.add_zero] using first
      | succ offset =>
        have equal : index + (offset + 1) = index + 1 + offset := by omega
        rw [equal]
        exact rest offset (by omega)
    · intro all
      refine ⟨by simpa only [Nat.add_zero] using all 0 (by omega), ?_⟩
      intro offset bounded
      have equal : index + 1 + offset = index + (offset + 1) := by omega
      rw [equal]
      exact all (offset + 1) (by omega)

end BulksketchBridge.Certificate
