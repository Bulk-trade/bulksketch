import BulksketchBridge.ProbeVerificationSpec
import BulksketchBridge.DegreeProbeRuntimeEncoding
import BulksketchBridge.Algebra.WordNative

namespace BulksketchBridge.ProbeVerification

open Aeneas Aeneas.Std Aeneas.Std.WP DegreeProbeRuntime DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract

set_option maxHeartbeats 1500000

/-- The callback models both generated fold closures without discarding any
element or changing their left-to-right accumulator order. -/
private theorem fold_stateless (callback : core.ops.function.FnMut Unit (U64 × U64) U64)
    (step : U64 → U64 → U64)
    (exactStep : ∀ a x, callback.call_mut () (a, x) = .ok (step a x, ()))
    (iter : core.slice.iter.Iter U64) (initial : U64) :
    Aeneas.Std.DegreeProbeRuntime.foldShared callback iter initial () =
      .ok ((iter.slice.val.drop iter.i).foldl step initial) := by
  have folded (words : List U64) (a : U64) :
      words.foldlM (fun ((acc, state) : U64 × Unit) x => callback.call_mut state (acc, x))
        (a, ()) = Result.ok (words.foldl step a, ()) := by
    induction words generalizing a with
    | nil => simp [List.foldlM_nil, pure]
    | cons head tail induction =>
      rw [List.foldlM_cons]
      change Aeneas.Std.bind (callback.call_mut () (a, head)) _ = _
      rw [exactStep, bind_ok]
      exact induction (step a head)
  unfold Aeneas.Std.DegreeProbeRuntime.foldShared
  simp only [folded, bind_ok]
  rfl

private theorem first_fold {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Slice U64) :
    Aeneas.Std.DegreeProbeRuntime.foldShared
      (bulksketch.decode.probe.verified.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64
        fieldDictionary kernels) ⟨roots, 0⟩ 0#u64 () =
        .ok (PortableEncoding.foldColumn roots.val 0 0#u64) := by
  refine fold_stateless _ (fun s x => s ^^^ x) ?_ _ _
  intro s x
  simp only [bulksketch.decode.probe.verified.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64.call_mut,
    lift, bind_ok]
  rfl

private theorem second_fold {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : ∀ x y, kernels.ArithmeticInst.mul x y = bulksketch.field.gf64.mul fieldDictionary x y)
    (square : ∀ x, kernels.ArithmeticInst.square x = bulksketch.field.gf64.square fieldDictionary x)
    (roots : Slice U64) :
    Aeneas.Std.DegreeProbeRuntime.foldShared
      (bulksketch.decode.probe.verified.closure_1.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64
        fieldDictionary kernels) ⟨roots, 0⟩ 0#u64 () =
        .ok (PortableEncoding.foldColumn roots.val 1 0#u64) := by
  refine fold_stateless _ (fun s x => s ^^^ PortableEncoding.oddPower x 1) ?_ _ _
  intro s x
  change bulksketch.decode.probe.verified.closure_1.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64.call_mut
    fieldDictionary kernels () (s, x) = _
  simp only [bulksketch.decode.probe.verified.closure_1.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64.call_mut,
    square, Square.square_refines, mul, Algebra.Gf64.native_mul_word, bind_ok, lift,
    PortableEncoding.oddPower, PortableEncoding.powerFrom, PortableEncoding.wordMul]
  rfl

private theorem slice_read (words : Slice U64) (index : Usize) (bound : index.val < words.length) :
    Slice.index_usize words index = .ok words[index.val]! := by
  obtain ⟨word, normal, equal⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words index bound)
  rw [normal, equal, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ bound)

private theorem equality_exact (left right : Slice U64) :
    Aeneas.Std.CertificateRuntime.mutableSharedEq
      (bulksketch.Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU64) left right =
      .ok (decide (left = right)) := by
  change core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU64 left right = _
  obtain ⟨equal, normal, meaning⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU64 left right (by
      intro x y; simp [liftFun2, spec_ok]))
  rw [normal]
  congr 1
  cases equal <;> simp_all

private theorem encoding_path {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (encoding : CorrectEncoding kernels) (odd roots scratch : Slice U64) (room : odd.length ≤ scratch.length) :
    (do
      let (window, back) ← core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice U64) scratch { «end» := odd.len }
      let words ← kernels.encode_nonzero window roots
      let result ← Aeneas.Std.CertificateRuntime.mutableSharedEq
        (bulksketch.Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU64) words odd
      .ok (result, back words)) =
      .ok (decide (encodedWords (prefixSlice scratch odd.length) roots = odd),
        restorePrefix scratch (encodedWords (prefixSlice scratch odd.length) roots)) := by
  have window := prefix_normal scratch odd.len (by simpa using room)
  rw [Slice.len_val] at window
  simp only [Slice.index_mut_SliceIndexRangeToUsizeSliceInst, window]
  change Aeneas.Std.bind (.ok (prefixSlice scratch odd.length, restorePrefix scratch)) _ = _
  rw [bind_ok]
  simp only [encoding (prefixSlice scratch odd.length) roots, equality_exact]
  change Aeneas.Std.bind (Result.ok (encodedWords (prefixSlice scratch odd.length) roots)) _ = _
  rw [bind_ok]
  change Aeneas.Std.bind (Result.ok (decide (encodedWords (prefixSlice scratch odd.length) roots = odd))) _ = _
  rw [bind_ok]

theorem verified_refines : ActualProbeVerified := by
  intro K kernels mul square encoding odd roots scratch bounds
  have zeroValue : (0#usize).val = 0 := rfl
  have oneValue : (1#usize).val = 1 := rfl
  have twoValue : (2#usize).val = 2 := rfl
  unfold bulksketch.decode.probe.verified expected
  simp only [UScalar.le_equiv, Slice.len_val, twoValue]
  by_cases small : roots.length ≤ 2
  · have readFirst := slice_read odd 0#usize (by simpa only [zeroValue] using bounds.firstRead small)
    simp only [zeroValue] at readFirst
    simp only [small, ite_true, core.slice.Slice.iter, bind_ok, first_fold kernels roots, readFirst]
    cases first : (PortableEncoding.foldColumn roots.val 0 0#u64 != odd[0]!)
    · simp only [Bool.false_eq_true, ite_false]
      by_cases two : 2 ≤ odd.length
      · have readSecond := slice_read odd 1#usize (by simp only [oneValue]; omega)
        simp only [oneValue] at readSecond
        simp only [two, ite_true, second_fold kernels mul square roots, bind_ok, readSecond]
        cases second : (PortableEncoding.foldColumn roots.val 1 0#u64 != odd[1]!)
        · have pass : precheckRejects odd roots = false := by
            simp only [precheckRejects, small, two, decide_true, first, second, Bool.true_and, Bool.false_or]
          simp only [Bool.false_eq_true, ite_false, pass]
          exact encoding_path kernels encoding odd roots scratch (bounds.encodingWindow pass)
        · simp only [precheckRejects, small, two, decide_true, first, second, Bool.true_and, Bool.false_or, ite_true]
      · have pass : precheckRejects odd roots = false := by
          simp only [precheckRejects, small, two, decide_true, decide_false, first, Bool.true_and,
            Bool.false_or, Bool.false_and]
        simp only [two, ite_false, pass, Bool.false_eq_true]
        exact encoding_path kernels encoding odd roots scratch (bounds.encodingWindow pass)
    · simp only [precheckRejects, small, decide_true, first, Bool.true_and, Bool.true_or, ite_true]
  · have pass : precheckRejects odd roots = false := by
      simp only [precheckRejects, small, decide_false, Bool.false_and]
    simp only [small, ite_false, pass, Bool.false_eq_true]
    exact encoding_path kernels encoding odd roots scratch (bounds.encodingWindow pass)

theorem verified_portable_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : ∀ x y, kernels.ArithmeticInst.mul x y = bulksketch.field.gf64.mul fieldDictionary x y)
    (square : ∀ x, kernels.ArithmeticInst.square x = bulksketch.field.gf64.square fieldDictionary x)
    (selectDefault : kernels.encode_nonzero = BulkKernels.encode_nonzero.default kernels)
    (insert : ∀ scratch roots, kernels.insert_nonzero scratch roots =
      bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
        fieldDictionary scratch roots)
    (odd roots scratch : Slice U64) (bounds : Bounds odd roots scratch) :
    bulksketch.decode.probe.verified fieldDictionary kernels odd roots scratch = .ok (expected odd roots scratch) :=
  verified_refines kernels mul square (encoding_of_portable_default kernels selectDefault insert) odd roots scratch bounds

end BulksketchBridge.ProbeVerification
