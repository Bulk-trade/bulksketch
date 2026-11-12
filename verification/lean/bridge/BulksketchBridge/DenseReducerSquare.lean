import BulksketchBridge.DenseReducerSquareSpec
import BulksketchBridge.DenseReducerTable
import BulksketchBridge.DenseMul
import BulksketchBridge.ClosedLeafAdvance
import BulksketchBridge.Square

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 4096

namespace BulksketchBridge.DenseReducerSquare

open bulksketch.backend.contract bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial

/-- The source high-coefficient accumulation and the existing convolution
row have identical monadic operations and mutable writeback. -/
theorem high_zip_is_convolution {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (iter : MutableZip.State bulksketch.types.RawProduct U64) (back : _ → _)
    (square : U64) :
    square_mod_into_loop0_loop0 field kernels iter back square =
      mul_into_loop0_loop0 field kernels iter back square := by
  rfl

/-- The source final reduction is the already proved mutable reduction loop. -/
theorem reduction_zip_is_convolution {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (iter : MutableZip.State U64 bulksketch.types.RawProduct) (back : _ → _) :
    square_mod_into_loop1 field kernels iter back = mul_into_loop1 field kernels iter back := by
  rfl

open BulksketchBridge BulksketchBridge.MutableZip DenseMulConvolutionSpec
open scoped BulksketchBridge.DenseMulReductionSpec

@[simp] theorem accumulateCoefficient_length (table : Slice U64) (degree index : Nat)
    (coefficient : U64) (raw : Slice Raw) :
    (accumulateCoefficient table degree index coefficient raw).length = raw.length := by
  by_cases low : index < (degree + 1) / 2 <;>
    simp only [accumulateCoefficient, low, ite_true, ite_false, Slice.setAtNat_length, mapFrom_length]

private theorem enumerate_active (a : Slice U64) (count : Usize) (active : count.val < a.length) :
    ∃ next : Usize, next.val = count.val + 1 ∧
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter U64) (iteratorAt a count) =
        .ok (some (count, a[count.val]!), iteratorAt a next) := by
  have safe : count.val + (1#usize).val ≤ Usize.max := by
    have capacity := a.length_ineq
    change a.length ≤ Usize.max at capacity
    simp only [show (1#usize).val = 1 by simp]
    omega
  obtain ⟨next, normal, value⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := count) (y := 1#usize) safe)
  have nextValue : next.val = count.val + 1 := by simpa using value
  have active' : count.val < (Slice.len a).val := by rwa [Slice.len_val]
  have inner : core.slice.iter.IteratorSliceIter.next ⟨a, count.val⟩ =
      .ok (some a[count.val]!, ⟨a, count.val + 1⟩) := by
    simp only [core.slice.iter.IteratorSliceIter.next, active', _root_.dite_true]
    exact congrArg (fun item => Result.ok (some item, (⟨a, count.val + 1⟩ : core.slice.iter.Iter U64)))
      (Slice.Inhabited_getElem_eq_getElem! a count.val active)
  refine ⟨next, nextValue, ?_⟩
  simp only [core.iter.adapters.enumerate.IteratorEnumerate.next, iteratorAt, inner,
    bind_ok, normal, nextValue]
  rfl

private theorem enumerate_done (a : Slice U64) (count : Usize) (done : a.length ≤ count.val) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter U64) (iteratorAt a count) =
      .ok (none, iteratorAt a count) := by
  have inactive : ¬ count.val < (Slice.len a).val := by rw [Slice.len_val]; omega
  have inner : core.slice.iter.IteratorSliceIter.next ⟨a, count.val⟩ =
      .ok (none, ⟨a, count.val⟩) := by
    simp only [core.slice.iter.IteratorSliceIter.next, inactive, _root_.dite_false]
  simp only [core.iter.adapters.enumerate.IteratorEnumerate.next, iteratorAt, inner, bind_ok]
  rfl

private theorem coefficient_step {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (rawLaw : RawMulAgrees kernels) (squareLaw : SquareAgrees kernels)
    (a table : Slice U64) (raw : Slice Raw) (count degree firstHigh : Usize)
    (active : count.val < a.length) (aBound : a.length ≤ degree.val)
    (firstHighVal : firstHigh.val = (degree.val + 1) / 2)
    (rawLen : raw.length = degree.val) (tableBound : degree.val / 2 * degree.val ≤ table.length) :
    ∃ next, next.val = count.val + 1 ∧
      square_mod_into_loop0.body dictionary kernels table degree firstHigh (iteratorAt a count) raw =
        .ok (.cont (iteratorAt a next, accumulateCoefficient table degree.val count.val a[count.val]! raw)) := by
  obtain ⟨next, nextValue, enumeration⟩ := enumerate_active a count active
  have squareNormal : kernels.ArithmeticInst.square a[count.val]! =
      .ok (Square.expectedWord a[count.val]!) := by
    rw [squareLaw, Square.square_refines]
  refine ⟨next, nextValue, ?_⟩
  simp only [square_mod_into_loop0.body, enumeration, bind_ok]
  dsimp! only
  simp only [squareNormal, bind_ok, UScalar.lt_equiv]
  by_cases low : count.val < firstHigh.val
  · have indexBound : 2 * count.val < raw.length := by omega
    have rawMax : raw.length ≤ Usize.max := raw.length_ineq
    obtain ⟨index, indexNormal, indexVal⟩ := RawMulTable.normal_of_spec _ _
      (Usize.mul_spec (x := 2#usize) (y := count) (by change 2 * count.val ≤ Usize.max; omega))
    change index.val = 2 * count.val at indexVal
    obtain ⟨value, read, readVal⟩ := RawMulTable.normal_of_spec _ _
      (Slice.index_usize_spec raw index (by omega))
    have old : value = raw[2 * count.val]! := by
      rw [← indexVal, ← Slice.Inhabited_getElem_eq_getElem! raw index.val (by omega)]
      exact readVal
    simp only [low, ite_true, indexNormal, bind_ok, read, lift, Slice.index_mut_usize, old]
    simp only [Bind.bind, bind_ok]
    dsimp! only
    simp only [Slice.set, indexVal, accumulateCoefficient, ← firstHighVal, low, ite_true]
  · have tableMax : table.length ≤ Usize.max := table.length_ineq
    have rowBound : (count.val - firstHigh.val) + 1 ≤ degree.val / 2 := by omega
    have endBound : ((count.val - firstHigh.val) + 1) * degree.val ≤ table.length :=
      (Nat.mul_le_mul_right degree.val rowBound).trans tableBound
    have startBound : (count.val - firstHigh.val) * degree.val ≤ table.length :=
      (Nat.mul_le_mul_right degree.val (by omega : count.val - firstHigh.val ≤ degree.val / 2)).trans tableBound
    obtain ⟨offset, sub, offsetVal, _⟩ := RawMulTable.normal_of_spec _ _
      (Usize.sub_spec (x := count) (y := firstHigh) (by omega))
    change offset.val = count.val - firstHigh.val at offsetVal
    obtain ⟨start, mul, startVal⟩ := RawMulTable.normal_of_spec _ _
      (Usize.mul_spec (x := offset) (y := degree) (by rw [offsetVal]; omega))
    change start.val = offset.val * degree.val at startVal
    rw [offsetVal] at startVal
    obtain ⟨stop, add, stopVal⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := start) (y := degree) (by rw [startVal]; rw [Nat.add_mul, Nat.one_mul] at endBound; omega))
    change stop.val = start.val + degree.val at stopVal
    have room : stop.val ≤ table.length := by
      simpa only [stopVal, startVal, Nat.add_mul, Nat.one_mul] using endBound
    let right := ClosedLeaf.region table start.val stop.val
    have read := ClosedLeaf.shared_region_normal table start stop (by omega) room
    have same : raw.length = right.length := by
      rw [ClosedLeaf.region_length _ _ _ room]
      omega
    obtain ⟨restore, returned, restored⟩ := DenseMulConvolution.inner_loop_refines kernels rawLaw
      (Square.expectedWord a[count.val]!) raw right same 0 (Nat.zero_le _) (fun state => state)
    rw [← high_zip_is_convolution] at returned
    simp only [low, ite_false, sub, mul, add, bind_ok, core.slice.Slice.iter_mut,
      Slice.index_SliceIndexRangeUsizeSliceInst, read]
    dsimp! only
    rw [construct raw right]
    simp only [bind_ok]
    dsimp! only
    rw [returned]
    simp only [bind_ok]
    dsimp! only
    rw [restored]
    simp only [stateAt, accumulateCoefficient, ← firstHighVal, low, ite_false, right, stopVal, startVal]

/-- Exact original outer pass from the next input word to exhaustion, using
the existing convolution row for the high table branch. -/
theorem coefficient_loop_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (rawLaw : RawMulAgrees kernels) (squareLaw : SquareAgrees kernels)
    (a table : Slice U64) (raw : Slice Raw) (count degree firstHigh : Usize)
    (aBound : a.length ≤ degree.val) (firstHighVal : firstHigh.val = (degree.val + 1) / 2)
    (rawLen : raw.length = degree.val) (tableBound : degree.val / 2 * degree.val ≤ table.length)
    (bounded : count.val ≤ a.length) :
    square_mod_into_loop0 dictionary kernels (iteratorAt a count) table degree raw firstHigh =
      .ok (accumulateSquare a table degree.val raw count.val (a.length - count.val)) := by
  suffices loopCase : ∀ remaining (index : Usize) (scratch : Slice Raw),
      index.val ≤ a.length → a.length - index.val = remaining → scratch.length = degree.val →
      square_mod_into_loop0 dictionary kernels (iteratorAt a index) table degree scratch firstHigh =
        .ok (accumulateSquare a table degree.val scratch index.val remaining) from
    loopCase _ count raw bounded rfl rawLen
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro index scratch bounded remainingEq scratchLen
    by_cases active : index.val < a.length
    · obtain ⟨next, nextValue, body⟩ := coefficient_step kernels rawLaw squareLaw a table scratch
        index degree firstHigh active aBound firstHighVal scratchLen tableBound
      have decrease : a.length - next.val < remaining := by omega
      have countEq : remaining = a.length - next.val + 1 := by omega
      let written := accumulateCoefficient table degree.val index.val a[index.val]! scratch
      rw [countEq, accumulateSquare, ← nextValue]
      conv => lhs; unfold square_mod_into_loop0 loop
      dsimp only
      rw [body]
      simp only [bind_ok]
      exact ih _ decrease next written (by omega) rfl (by simp [written, scratchLen])
    · have stopped : a.length ≤ index.val := by omega
      have finished : remaining = 0 := by omega
      rw [finished, accumulateSquare]
      conv => lhs; unfold square_mod_into_loop0 loop
      dsimp only
      simp only [square_mod_into_loop0.body, enumerate_done a index stopped, bind_ok]
      dsimp! only
      simp only [bind_ok]

open DenseCoefficient RebuiltLfsr DenseNormalization

private theorem ceil_half (degree : Usize) :
    ∃ result : Usize, bulksketch.DenseReducerSquareRuntime.divCeil degree 2#usize = .ok result ∧
      result.val = (degree.val + 1) / 2 := by
  obtain ⟨quotient, divNormal, divVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.div_spec degree (y := 2#usize) (by simp))
  obtain ⟨remainder, remNormal, remVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.rem_spec degree (y := 2#usize) (by simp))
  change quotient.val = degree.val / 2 at divVal
  change remainder.val = degree.val % 2 at remVal
  have max : degree.val ≤ Usize.max := by scalar_tac
  simp only [bulksketch.DenseReducerSquareRuntime.divCeil, divNormal, remNormal, bind_ok, UScalar.lt_equiv]
  change ∃ result, (if 0 < remainder.val then quotient + 1#usize else .ok quotient) =
    .ok result ∧ result.val = (degree.val + 1) / 2
  by_cases hasRemainder : 0 < remainder.val
  · obtain ⟨successor, added, value⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := quotient) (y := 1#usize) (by change quotient.val + 1 ≤ Usize.max; omega))
    change successor.val = quotient.val + 1 at value
    exact ⟨successor, by simp only [hasRemainder, ite_true, added], by omega⟩
  · exact ⟨quotient, by simp only [hasRemainder, ite_false], by omega⟩

private theorem raw_prefix (raw : Slice Raw) (count : Usize) (bound : count.val ≤ raw.length) :
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut ⟨count⟩ raw =
      .ok (DenseMul.takeSlice raw count.val, fun replacement => raw.setSlice! 0 replacement.val) := by
  obtain ⟨⟨window, back⟩, normal, values, _, restore⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeToUsizeSlice.index_mut.step_spec ⟨count⟩ raw bound)
  have exactWindow : window = DenseMul.takeSlice raw count.val := by
    apply Slice.ext
    simpa only [DenseMul.takeSlice, Slice.from_val, List.slice_zero_j] using values
  have exactBack : back = fun replacement => raw.setSlice! 0 replacement.val := by
    funext replacement
    apply Slice.ext
    simpa only [Slice.setSlice!_val] using restore replacement
  rw [normal, exactWindow, exactBack]

private theorem fill_raw (raw : Slice Raw) (degree : Nat) :
    core.slice.Slice.fill bulksketch.types.RawProduct.Insts.CoreCloneClone
      (DenseMul.takeSlice raw degree) DenseMul.zeroProduct = .ok (zeroRaw raw degree) := by
  obtain ⟨output, normal, length, values⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.Slice.fill.spec bulksketch.types.RawProduct.Insts.CoreCloneClone
      (DenseMul.takeSlice raw degree) DenseMul.zeroProduct (by exact (WP.spec_ok _).mpr rfl))
  have equal : output = zeroRaw raw degree := by
    apply Slice.ext
    simpa only [zeroRaw, Slice.from_val, DenseMul.take_length] using values
  rw [normal, equal]

@[simp] theorem accumulateSquare_length (a table : Slice U64) (degree : Nat)
    (raw : Slice Raw) (index count : Nat) :
    (accumulateSquare a table degree raw index count).length = raw.length := by
  induction count generalizing raw index with
  | zero => rfl
  | succ count ih => simp only [accumulateSquare, ih, accumulateCoefficient_length]

private theorem normalize_output (out : Slice U64) (degree : Nat) :
    bulksketch.poly.dense.normalized_len (prefixSlice out degree) = .ok (outputLength out degree) := by
  let words := prefixSlice out degree
  obtain ⟨size, normal, value⟩ := normalized_len_refines words
  have bound : normalizedLength words.val ≤ Usize.max :=
    (normalizedLength_le _).trans words.length_ineq
  have exactSize : size = outputLength out degree := by
    apply UScalar.eq_of_val_eq
    exact value.trans (ClosedLeafAdvance.word_val _ bound).symm
  rw [normal, exactSize]

/-- Conditional exact original wrapper. The selected backend's result
is a separate premise; the source's true branch preserves its scratch
return and the false branch performs the full original scalar fallback. -/
theorem square_mod_into_refines : ActualSquareModInto := by
  intro K kernels rawLaw squareLaw reduceLaw a modulus table dst raw minModulus monic aRoom
    dstRoom rawRoom tableLen accelerated active returnedRaw called rawResultRoom
  let degreeNat := modulus.length - 1
  have rawMax : raw.length ≤ Usize.max := raw.length_ineq
  have tableMax : table.length ≤ Usize.max := table.length_ineq
  have minCheck : (4#usize : Usize) ≤ Slice.len modulus := by scalar_tac
  obtain ⟨degree, degreeNormal, degreeVal, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := Slice.len modulus) (y := 1#usize) (by scalar_tac))
  rw [Slice.len_val] at degreeVal
  change degree.val = degreeNat at degreeVal
  have inputCheck : Slice.len a ≤ degree := by
    rw [UScalar.le_equiv, Slice.len_val, degreeVal]
    exact aRoom
  have dstCheck : degree ≤ Slice.len dst := by
    rw [UScalar.le_equiv, Slice.len_val, degreeVal]
    exact dstRoom
  obtain ⟨double, doubleNormal, doubleVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := 2#usize) (y := degree) (by change 2 * degree.val ≤ Usize.max; rw [degreeVal]; omega))
  have rawCheck : double < Slice.len raw := by
    rw [UScalar.lt_equiv, Slice.len_val, doubleVal]
    change 2 * degree.val < raw.length
    rwa [degreeVal]
  obtain ⟨half, halfNormal, halfVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.div_spec degree (y := 2#usize) (by simp))
  change half.val = degree.val / 2 at halfVal
  obtain ⟨total, totalNormal, totalVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := degree) (y := half) (by rw [halfVal, degreeVal, ← tableLen]; exact tableMax))
  have tableCheck : Slice.len table = total := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val, totalVal, halfVal, degreeVal, tableLen]
  have last : bulksketch.DenseReducerTableRuntime.last modulus = .ok (some 1#u64) := by
    unfold bulksketch.DenseReducerTableRuntime.last
    rw [List.getLast?_eq_getElem?]
    have inRange : modulus.val.length - 1 < modulus.val.length := by
      change modulus.length - 1 < modulus.length
      omega
    rw [List.getElem?_eq_getElem inRange]
    rw [List.Inhabited_getElem_eq_getElem! _ _ inRange, ← Slice.getElem!_Nat_eq]
    exact congrArg (fun v => Result.ok (some v)) monic
  have compare : bulksketch.DenseReducerTableRuntime.optionEq
      (core.cmp.PartialEqShared core.cmp.PartialEqU64) (some 1#u64) (some 1#u64) = .ok true := rfl
  have firstCut := prefix_normal dst degree (by rwa [degreeVal])
  have calledAtDegree : kernels.square_mod a table (prefixSlice dst degree.val) raw =
      .ok (accelerated, active, returnedRaw) := by rw [degreeVal]; exact called
  let dst1 := restorePrefix dst active
  have dst1Len : dst1.length = dst.length := restore_length _ _
  simp only [square_mod_into, massert, minCheck, ite_true, last, bind_ok, compare,
    degreeNormal, inputCheck, dstCheck, doubleNormal, rawCheck, halfNormal, totalNormal, tableCheck,
    Slice.index_mut_SliceIndexRangeToUsizeSliceInst, firstCut]
  dsimp! only
  simp only [calledAtDegree, bind_ok]
  dsimp! only
  cases accelerated with
  | true =>
    have read := shared_prefix_normal dst1 degree (by rwa [dst1Len, degreeVal])
    simp only [expectedOutput, ite_true, Slice.index_SliceIndexRangeToUsizeSliceInst,
      show restorePrefix dst active = dst1 by rfl, read, bind_ok, normalize_output]
    simp only [degreeVal, degreeNat]
  | false =>
    have rawEnough : degree.val ≤ returnedRaw.length := by
      rw [degreeVal]
      exact rawResultRoom rfl
    have rawCut := raw_prefix returnedRaw degree rawEnough
    have cleared := fill_raw returnedRaw degree.val
    let zero := zeroRaw returnedRaw degree.val
    have zeroLen : zero.length = degree.val := by
      simp only [zero, zeroRaw, Slice.length, Slice.from_val, List.length_replicate, Nat.min_eq_left rawEnough]
    obtain ⟨firstHigh, firstHighNormal, firstHighVal⟩ := ceil_half degree
    have tableRoom : degree.val / 2 * degree.val ≤ table.length := by
      rw [degreeVal, Nat.mul_comm, ← tableLen]
    have scalar := coefficient_loop_refines kernels rawLaw squareLaw a table zero 0#usize degree firstHigh
      (by rwa [degreeVal]) firstHighVal zeroLen tableRoom (by simp)
    let acc := accumulateSquare a table degree.val zero 0 a.length
    have accLen : acc.length = degree.val := by simp only [acc, accumulateSquare_length, zeroLen]
    have secondCut := prefix_normal dst1 degree (by rwa [dst1Len, degreeVal])
    let window := prefixSlice dst1 degree.val
    have windowLen : window.length = degree.val :=
      (prefix_length _ _).trans (Nat.min_eq_left (by rwa [dst1Len, degreeVal]))
    have zipped :
        bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default
          (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
          (core.iter.traits.collect.IntoIterator.Blanket (core.iter.traits.iterator.IteratorSliceIter Raw))
          ⟨window, 0⟩ ⟨acc, 0⟩ =
            .ok (stateAt window acc 0, fun state => state.fst) := by
      simp only [bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default,
        Aeneas.Std.MutableZip.construct,
        core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_ok, stateAt]
    obtain ⟨restore, reduced, restored⟩ := DenseMulReduction.loop_refines
      kernels reduceLaw window acc (windowLen.trans accLen.symm) 0 (Nat.zero_le _) (fun state => state)
    rw [← reduction_zip_is_convolution] at reduced
    let out := restorePrefix dst1 (mapFrom window acc (fun _ product => DenseMulReductionSpec.reduceWord product) 0)
    have outLen : out.length = dst.length := by simp only [out, restore_length, dst1Len]
    have read := shared_prefix_normal out degree (by rwa [outLen, degreeVal])
    have defaultRaw : bulksketch.types.RawProduct.Insts.CoreDefaultDefault.default =
        .ok DenseMul.zeroProduct := rfl
    simp only [Bool.false_eq_true, ite_false, rawCut, bind_ok]
    dsimp! only
    simp only [defaultRaw, cleared, firstHighNormal, core.slice.Slice.iter,
      core.iter.traits.iterator.Iterator.enumerate.trait_default,
      core.iter.traits.iterator.Iterator.enumerate.default, bind_ok]
    change (do
      let accumulators ← square_mod_into_loop0 dictionary kernels (iteratorAt a 0#usize) table degree zero firstHigh
      let (s, back) ← core.slice.index.SliceIndexRangeToUsizeSlice.index_mut ⟨degree⟩ dst1
      let (im, iterBack) ← core.slice.Slice.iter_mut s
      let (iter, zipBack) ← bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default
        (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
        (core.iter.traits.collect.IntoIterator.Blanket (core.iter.traits.iterator.IteratorSliceIter Raw))
        im ⟨accumulators, 0⟩
      let (last, finish) ← square_mod_into_loop1 dictionary kernels iter (fun state => state)
      let dst2 := back (iterBack (zipBack (finish last)))
      let s4 ← core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨degree⟩ dst2
      let size ← bulksketch.poly.dense.normalized_len s4
      .ok (size, dst2, returnedRaw.setSlice! 0 accumulators.val)) = _
    have scalarAtAcc : square_mod_into_loop0 dictionary kernels (iteratorAt a 0#usize) table degree zero firstHigh =
        .ok acc := by
      have zeroValue : (0#usize : Usize).val = 0 := by simp
      simpa only [acc, zeroValue, Nat.sub_zero] using scalar
    simp only [scalarAtAcc, secondCut, Bind.bind, bind_ok]
    simp only [core.slice.Slice.iter_mut, bind_ok]
    try dsimp! only
    rw [zipped]
    simp only [bind_ok]
    rw [reduced]
    simp only [bind_ok]
    rw [restored]
    change (do
      let words ← core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨degree⟩ out
      let size ← bulksketch.poly.dense.normalized_len words
      .ok (size, out, returnedRaw.setSlice! 0 acc.val)) = _
    simp only [read, Bind.bind, bind_ok, normalize_output, expectedOutput, ite_false]
    dsimp only [out, acc, window, zero, dst1]
    simp only [degreeVal, degreeNat, Bool.false_eq_true, ite_false]

end BulksketchBridge.DenseReducerSquare
