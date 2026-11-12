import Arithmetic.DenseDivRemGenerated
import BulksketchBridge.DenseDivRemDescending
import BulksketchBridge.DenseDivRemRows
import BulksketchBridge.DenseDivRemReduction
import BulksketchBridge.DenseDivRemCursor
import BulksketchBridge.DenseDivisionComposition
import BulksketchBridge.DenseReducerSquare

namespace BulksketchBridge.DenseDivRem

open Aeneas Aeneas.Std BulksketchBridge DenseDivision DenseCoefficient RebuiltLfsr MutableZip
open bulksketch.backend.contract
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial
open scoped BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem last_normal (b : Slice U64) (positive : 0 < b.length) :
    bulksketch.DenseReducerTableRuntime.last b = .ok (some b[b.length - 1]!) := by
  unfold bulksketch.DenseReducerTableRuntime.last
  rw [List.getLast?_eq_getElem?]
  have bound : b.val.length - 1 < b.val.length := by change b.length - 1 < b.length; omega
  rw [List.getElem?_eq_getElem bound, List.Inhabited_getElem_eq_getElem! _ _ bound, ← Slice.getElem!_Nat_eq]

private theorem cut_prefix (raw : Slice Raw) (length : Usize) (room : length.val ≤ raw.length) :
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut ⟨length⟩ raw =
      .ok (DenseMul.takeSlice raw length.val, fun (replacement : Slice Raw) => raw.setSlice! 0 replacement.val) := by
  obtain ⟨⟨window, restore⟩, normal, values, _, update⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeToUsizeSlice.index_mut.step_spec ⟨length⟩ raw room)
  have windowEq : window = DenseMul.takeSlice raw length.val := by
    rw [Slice.eq_iff]
    simpa only [DenseMul.takeSlice, Slice.from_val, List.slice_zero_j] using values
  have restoreEq : restore = fun (replacement : Slice Raw) => raw.setSlice! 0 replacement.val := by
    funext replacement
    rw [Slice.eq_iff]
    simpa only [Slice.setSlice!_val] using update replacement
  rw [normal, windowEq, restoreEq]

private theorem reduced_words (dst : Slice U64) (raw : Slice Raw) (count : Nat)
    (dstLen : dst.length = count) (rawRoom : count ≤ raw.length) :
    mapFrom dst raw (fun _ product => DenseMulReductionSpec.reduceWord product) 0 = remainderWords raw count := by
  have normalized := remainder_words_length raw count rawRoom
  apply Slice.ext_getElem ((mapFrom_length _ _ _ _).trans (dstLen.trans normalized.symm))
  intro i mappedBound remBound
  have below : i < count := by omega
  have rightEq : (remainderWords raw count)[i]! = DenseMulReductionSpec.reduceWord raw[i]! := by
    simp only [remainderWords, Slice.getElem!_Nat_eq, Slice.from_val, Nat.min_eq_left rawRoom]
    rw [← List.Inhabited_getElem_eq_getElem! _ i (by simpa only [List.length_ofFn] using below), List.getElem_ofFn]
    rfl
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ mappedBound,
    Slice.Inhabited_getElem_eq_getElem! _ _ remBound, mapFrom_word _ _ _ _ _ (by omega),
    ite_eq_left (Nat.zero_le _), rightEq]

private theorem output_normal (words : Slice U64) (count : Nat) (room : count ≤ words.length) :
    bulksketch.poly.dense.normalized_len (prefixSlice words count) =
      .ok (DenseReducerSquare.outputLength words count) := by
  obtain ⟨result, normal, value⟩ := DenseNormalization.normalized_len_refines (prefixSlice words count)
  have exactValue : result = DenseReducerSquare.outputLength words count := by
    apply UScalar.eq_of_val_eq
    rw [value, normalized_value words count room]
    simp only [prefixSlice, Slice.from_val]
  rw [normal, exactValue]

/-- The original unoutlined Dense wrapper with checked loops and exact scratch writebacks. -/
theorem direct_div_rem_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : MulWordLaw kernels) (rawMul : DenseMulConvolutionSpec.RawMulAgrees kernels)
    (reduce : DenseMul.reduceAgrees kernels) (inverseLaw : BmTerminal.NativeInverse kernels) :
    RefinesModel (fun {_ _} => div_rem_into) kernels := by
  intro a b q rem raw positive leading qRoom remRoom rawRoom
  let inverse := divisorInverse b[b.length - 1]!
  change div_rem_into dictionary kernels a b q rem raw =
    .ok (expectedDivRem a b q rem raw inverse)
  have inv := native_inverse kernels inverseLaw b[b.length - 1]! leading
  have leadingOk : core.option.Option.expect (some b[b.length - 1]!)
      (toStr "zero polynomial divisor") = .ok b[b.length - 1]! := rfl
  have qMax : q.length ≤ Usize.max := q.length_ineq
  obtain ⟨size, addOk, sizeValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := Slice.len a) (y := 1#usize) (by
      rw [Slice.len_val]; change a.length + 1 ≤ Usize.max; omega))
  rw [Slice.len_val] at sizeValue
  change size.val = a.length + 1 at sizeValue
  obtain ⟨degree, subOk, degreeValue, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := Slice.len b) (y := 1#usize) (by rw [Slice.len_val]; change 1 ≤ b.length; omega))
  rw [Slice.len_val] at degreeValue
  change degree.val = b.length - 1 at degreeValue
  have qCheck : size ≤ Slice.len q := by rw [UScalar.le_equiv, Slice.len_val, sizeValue]; exact qRoom
  have remCheck : size ≤ Slice.len rem := by rw [UScalar.le_equiv, Slice.len_val, sizeValue]; exact remRoom
  have rawCheck : size ≤ Slice.len raw := by rw [UScalar.le_equiv, Slice.len_val, sizeValue]; exact rawRoom
  have qCut := prefix_normal q size (by omega)
  have remCut := prefix_normal rem size (by omega)
  let startQ := cleared q size.val
  let startRem := cleared rem size.val
  let startRaw := initialRaw a raw
  let rawWindow := DenseMul.takeSlice raw a.length
  have rawWindowWidth : rawWindow.length = a.length := by
    simp [rawWindow, Nat.min_eq_left (show a.length ≤ raw.length by omega)]
  have rawCut := cut_prefix raw (Slice.len a) (by rw [Slice.len_val]; omega)
  have zippedInit :
      bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default
        (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT Raw)
        (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U64)
        ⟨DenseMul.takeSlice raw a.length, 0⟩ a = .ok (stateAt rawWindow a 0, fun state => state.fst) := by
    simp only [bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default,
      Aeneas.Std.MutableZip.construct, SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
      bind_ok, stateAt, rawWindow]
  have initNormal := init_loop rawWindow a rawWindowWidth 0 (Nat.zero_le _) (fun z => z)
  have modelRaw : raw.setSlice! 0 (mapFrom rawWindow a initWord 0).val = startRaw := by
    unfold startRaw initialRaw
    congr 2
    apply List.ext_getElem (by simp [rawWindowWidth])
    intro i leftBound rightBound
    have idx : i < rawWindow.length := by rw [rawWindowWidth]; simpa using rightBound
    rw [List.Inhabited_getElem_eq_getElem! _ i leftBound, ← Slice.getElem!_Nat_eq,
      mapFrom_word _ _ _ _ _ idx, ite_eq_left (Nat.zero_le _), List.getElem_map,
      List.Inhabited_getElem_eq_getElem! _ _ (by simpa using rightBound), ← Slice.getElem!_Nat_eq]
    rfl
  have startRawLen : startRaw.length = raw.length := Slice.setSlice!_length ..
  let count := a.length - degree.val
  let out := descend b degree.val inverse count startQ startRaw
  have initialIter :
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
        ⟨degree, Slice.len a⟩ = .ok (reverseRange degree (Slice.len a)) := rfl
  have descending :
      div_rem_into_loop1 dictionary kernels (reverseRange degree (Slice.len a))
        b startQ startRaw inverse degree = .ok out := by
    by_cases active : degree.val ≤ a.length
    · exact descending_loop kernels mul reduce rawMul b startQ startRaw inverse degree (Slice.len a) count
        (by rw [Slice.len_val]; unfold count; omega)
        (by unfold startQ count; rw [cleared_length]; omega)
        (by rw [Slice.len_val, startRawLen]; omega) (by omega)
    · have exhausted := descending_done kernels b startQ startRaw inverse degree (Slice.len a)
        (by rw [Slice.len_val]; omega)
      have none : count = 0 := by unfold count; omega
      simpa only [out, none, descend] using exhausted
  have ⟨qLen, scratchLen⟩ := descend_widths b degree.val count inverse startQ startRaw
  change out.1.length = startQ.length at qLen
  change out.2.length = startRaw.length at scratchLen
  let remSize := core.cmp.impls.OrdUsize.min degree (Slice.len a)
  have remValue : remSize.val = min degree.val a.length := by
    simp only [remSize, core.cmp.impls.OrdUsize.min_val, Slice.len_val]
  have remBound : remSize.val ≤ startRem.length := by
    unfold startRem
    rw [cleared_length, remValue]
    omega
  have scratchRoom : remSize.val ≤ out.2.length := by
    rw [scratchLen, startRawLen, remValue]
    omega
  have remOutCut := prefix_normal startRem remSize remBound
  let window := prefixSlice startRem remSize.val
  have windowLen : window.length = remSize.val :=
    (prefix_length _ _).trans (Nat.min_eq_left remBound)
  have zipped :
      bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default
        (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
        (core.iter.traits.collect.IntoIterator.Blanket (core.iter.traits.iterator.IteratorSliceIter Raw))
        ⟨window, 0⟩ ⟨out.2, 0⟩ =
          .ok (stateAt window out.2 0, fun state => state.fst) := by
    simp only [bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default,
      Aeneas.Std.MutableZip.construct, core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_ok, stateAt]
  obtain ⟨restore, reduced, restored⟩ := prefix_reduction_loop kernels reduce window out.2 (by omega)
    0 (Nat.zero_le _) (fun state => state)
  have qRoom' : size.val ≤ out.1.length := by rw [qLen, cleared_length, sizeValue]; exact qRoom
  let remOut := restorePrefix startRem (remainderWords out.2 remSize.val)
  have remOutRoom : remSize.val ≤ remOut.length := by unfold remOut; rw [restore_length]; exact remBound
  have qRead := shared_prefix_normal out.1 size qRoom'
  have remRead := shared_prefix_normal remOut remSize remOutRoom
  simp only [div_rem_into, last_normal b positive, bind_ok, leadingOk,
    inv, addOk, massert, qCheck, remCheck, rawCheck, ite_true,
    Slice.index_mut_SliceIndexRangeToUsizeSliceInst, qCut, remCut, rawCut]
  dsimp! only
  simp only [fill_zero, bind_ok, core.slice.Slice.iter_mut, Slice.len_val]
  dsimp! only
  rw [zippedInit]
  simp only [bind_ok]
  dsimp! only
  rw [initNormal]
  simp only [bind_ok, subOk, initialIter, lift, core.slice.Slice.iter, stateAt, modelRaw]
  change (do
    let (nextQ, scratch) ← div_rem_into_loop1 dictionary kernels (reverseRange degree (Slice.len a)) b startQ startRaw inverse degree
    let (win, back) ← core.slice.index.SliceIndexRangeToUsizeSlice.index_mut ⟨remSize⟩ startRem
    let (z, zipBack) ← bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default
      (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
      (core.iter.traits.collect.IntoIterator.Blanket (core.iter.traits.iterator.IteratorSliceIter Raw))
      ⟨win, 0⟩ ⟨scratch, 0⟩
    let (last, finish) ← div_rem_into_loop2 dictionary kernels z id
    let qPrefix ← core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨size⟩ nextQ
    let qSize ← bulksketch.poly.dense.normalized_len qPrefix
    let outRem := back ((zipBack (finish last)).slice)
    let remPrefix ← core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨remSize⟩ outRem
    let remLen ← bulksketch.poly.dense.normalized_len remPrefix
    .ok ((qSize, remLen), nextQ, outRem, scratch)) = _
  have descendingPair :
      div_rem_into_loop1 dictionary kernels (reverseRange degree (Slice.len a))
        b startQ startRaw inverse degree = .ok (out.1, out.2) := descending
  simp only [descendingPair, remOutCut, Bind.bind, bind_ok]
  change (do
    let (z, zipBack) ← bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default
      (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
      (core.iter.traits.collect.IntoIterator.Blanket (core.iter.traits.iterator.IteratorSliceIter Raw))
      ⟨window, 0⟩ ⟨out.2, 0⟩
    let (last, finish) ← div_rem_into_loop2 dictionary kernels z id
    let qPrefix ← core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨size⟩ out.1
    let qSize ← bulksketch.poly.dense.normalized_len qPrefix
    let remOut' := restorePrefix startRem ((zipBack (finish last)).slice)
    let remPrefix ← core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨remSize⟩ remOut'
    let remLen ← bulksketch.poly.dense.normalized_len remPrefix
    .ok ((qSize, remLen), out.1, remOut', out.2)) = _
  have reducedExact :
      div_rem_into_loop2 dictionary kernels (stateAt window out.2 0) id =
        .ok (stateAt window out.2 window.length, restore) := by
    exact reduced
  simp only [zipped, Bind.bind, bind_ok]
  rw [reducedExact]
  simp only [bind_ok]
  have restoredExact :
      (restore ⟨⟨window, window.length⟩, ⟨out.2, window.length⟩⟩).fst.slice =
        remainderWords out.2 remSize.val := by
    exact (congrArg (fun s => s.fst.slice) restored).trans
      (reduced_words window out.2 remSize.val windowLen scratchRoom)
  simp only [stateAt, qRead, bind_ok]
  rw [restoredExact]
  change (do
    let qSize ← bulksketch.poly.dense.normalized_len (prefixSlice out.1 size.val)
    let remPrefix ← core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨remSize⟩ remOut
    let remLen ← bulksketch.poly.dense.normalized_len remPrefix
    .ok ((qSize, remLen), out.1, remOut, out.2)) = _
  simp only [output_normal out.1 size.val qRoom', remRead, Bind.bind, bind_ok]
  rw [output_normal remOut remSize.val remOutRoom]
  simp only [bind_ok]
  simp only [expectedDivRem, remOut, remValue, out, count, degreeValue, startQ, startRem, sizeValue, startRaw, inverse]

end BulksketchBridge.DenseDivRem
