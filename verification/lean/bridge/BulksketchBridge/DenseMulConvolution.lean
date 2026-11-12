import BulksketchBridge.DenseMulConvolutionSpec
import BulksketchBridge.RawMul

namespace BulksketchBridge.DenseMulConvolution

open Aeneas Aeneas.Std BulksketchBridge.MutableZip DenseMulConvolutionSpec
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial
open scoped BulksketchBridge.DenseMulReductionSpec

/-- The original row loop accumulates both raw halves through its backward
callback. The right slice and all earlier window slots are preserved before
the incoming callback runs. -/
theorem inner_loop_refines : innerLoopFrame := by
  intro K kernels rawMulAgrees left window b same start bounded back
  have rawNormal (right : U64) : kernels.ArithmeticInst.raw_mul left right =
      Result.ok (RawMul.expectedProduct left right) := by
    rw [rawMulAgrees left right, RawMul.raw_mul_refines]
  suffices ∀ remaining start, start ≤ window.length → window.length - start = remaining →
      ∀ back : State bulksketch.types.RawProduct U64 → State bulksketch.types.RawProduct U64,
        ∃ restore : State bulksketch.types.RawProduct U64 → State bulksketch.types.RawProduct U64,
          mul_into_loop0_loop0 dictionary kernels (stateAt window b start) back left =
            Result.ok (stateAt window b window.length, restore) ∧
          restore (stateAt window b window.length) = back (stateAt
            (mapFrom window b (fun old right => xorProduct old (RawMul.expectedProduct left right)) start)
            b window.length)
    from this (window.length - start) start bounded rfl back
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro start bounded count back
    by_cases active : start < window.length
    · have rightBound : start < b.length := by omega
      have step : mul_into_loop0_loop0.body dictionary kernels left (stateAt window b start) back =
          Result.ok (ControlFlow.cont (stateAt window b (start + 1), fun final =>
            back (replaceLeft final start (xorProduct window[start]! (RawMul.expectedProduct left b[start]!))))) := by
        simp only [mul_into_loop0_loop0.body, next_some_at window b start active rightBound, bind_ok]
        dsimp! only
        rw [Slice.Inhabited_getElem_eq_getElem! b start rightBound,
          Slice.Inhabited_getElem_eq_getElem! window start active, rawNormal]
        simp only [bind_ok, lift, xorProduct]
      obtain ⟨restore, returns, meaning⟩ := ih (window.length - (start + 1)) (by omega)
        (start + 1) (by omega) rfl
        (fun final => back (replaceLeft final start (xorProduct window[start]! (RawMul.expectedProduct left b[start]!))))
      refine ⟨restore, ?_, ?_⟩
      · unfold mul_into_loop0_loop0 loop
        dsimp only
        rw [step]
        simp only [bind_ok]
        exact returns
      · rw [meaning, apply_step window b (fun old right => xorProduct old (RawMul.expectedProduct left right)) start active]
    · have terminal : start = window.length := by omega
      subst start
      refine ⟨back, ?_, ?_⟩
      · unfold mul_into_loop0_loop0 loop
        dsimp only
        simp only [mul_into_loop0_loop0.body,
          next_done_at window b window.length (Or.inl (Nat.le_refl _)), bind_ok]
        dsimp! only
        simp only [bind_ok]
      · rw [mapFrom_full_length]

private theorem restore_row (left : U64) (b : Slice U64)
    (raw window : Slice bulksketch.types.RawProduct) (offset : Nat)
    (room : offset + b.length ≤ raw.length)
    (windowValues : window.val = raw.val.slice offset (offset + b.length))
    (windowLength : window.length = b.length) :
    raw.setSlice! offset
      (mapFrom window b (fun old right => xorProduct old (RawMul.expectedProduct left right)) 0).val =
      row left b raw offset := by
  let mapped := mapFrom window b (fun old right => xorProduct old (RawMul.expectedProduct left right)) 0
  have mappedLength : mapped.val.length = b.length := by
    change mapped.length = b.length
    exact (mapFrom_length _ _ _ _).trans windowLength
  apply Slice.ext_getElem (by simp)
  intro slot restoredBound outputBound
  have slotBound : slot < raw.length := by simpa using outputBound
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ restoredBound,
    Slice.Inhabited_getElem_eq_getElem! _ _ outputBound, row_word _ _ _ _ _ slotBound]
  change (raw.setSlice! offset mapped.val)[slot]! = _
  unfold rowWord
  by_cases inside : offset ≤ slot ∧ slot < offset + b.length
  · rw [ite_eq_left inside,
      Slice.setSlice!_getElem!_middle raw mapped.val offset slot (by rw [mappedLength]; omega)]
    rw [← Slice.getElem!_Nat_eq]
    change (mapFrom window b (fun old right => xorProduct old (RawMul.expectedProduct left right)) 0)[slot - offset]! = _
    rw [mapFrom_word _ _ _ _ _ (by omega), ite_eq_left (Nat.zero_le _)]
    have old : window[slot - offset]! = raw[slot]! := by
      simp only [Slice.getElem!_Nat_eq, windowValues]
      rw [List.getElem!_slice offset (offset + b.length) (slot - offset) raw.val (by
        change offset + b.length ≤ raw.length ∧ offset + (slot - offset) < offset + b.length
        omega)]
      rw [show offset + (slot - offset) = slot by omega]
    rw [old]
  · rw [ite_eq_right inside]
    by_cases before : slot < offset
    · exact Slice.setSlice!_getElem!_prefix raw mapped.val offset slot before
    · exact Slice.setSlice!_getElem!_suffix raw mapped.val offset slot (by rw [mappedLength]; omega)

private theorem enumerate_step (a : Slice U64) (count : Usize) (active : count.val < a.length) :
    ∃ next : Usize, next.val = count.val + 1 ∧
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter U64) (iteratorAt a count) =
        Result.ok (some (count, a[count.val]!), iteratorAt a next) := by
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
      Result.ok (some a[count.val]!, ⟨a, count.val + 1⟩) := by
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
      Result.ok (none, iteratorAt a count) := by
  have inactive : ¬ count.val < (Slice.len a).val := by rw [Slice.len_val]; omega
  have inner : core.slice.iter.IteratorSliceIter.next ⟨a, count.val⟩ =
      Result.ok (none, ⟨a, count.val⟩) := by
    simp only [core.slice.iter.IteratorSliceIter.next, inactive, _root_.dite_false]
  simp only [core.iter.adapters.enumerate.IteratorEnumerate.next, iteratorAt, inner, bind_ok]
  rfl

private theorem outer_step {K : Type}
    (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (rawMulAgrees : RawMulAgrees kernels) (a b : Slice U64)
    (raw : Slice bulksketch.types.RawProduct) (count : Usize)
    (active : count.val < a.length) (room : a.length + b.length ≤ raw.length) :
    ∃ next : Usize, next.val = count.val + 1 ∧
      mul_into_loop0.body dictionary kernels b (iteratorAt a count) raw =
      Result.ok (ControlFlow.cont (iteratorAt a next, row a[count.val]! b raw count.val)) := by
  obtain ⟨next, nextValue, enumeration⟩ := enumerate_step a count active
  have safe : count.val + (Slice.len b).val ≤ Usize.max := by
    have capacity := raw.length_ineq
    change raw.length ≤ Usize.max at capacity
    rw [Slice.len_val]
    omega
  obtain ⟨stop, addNormal, addValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := count) (y := Slice.len b) safe)
  have stopValue : stop.val = count.val + b.length := by simpa only [Slice.len_val] using addValue
  have ordered : count ≤ stop := by
    apply (UScalar.le_equiv _ _).mpr
    omega
  have stopBound : stop.val ≤ raw.length := by omega
  obtain ⟨⟨window, writeBack⟩, windowNormal, windowValues, windowLength, writeBackExact⟩ :=
    RawMulTable.normal_of_spec _ _ (core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec
      { start := count, «end» := stop } raw ordered stopBound)
  have same : window.length = b.length := by
    rw [windowLength]
    change stop.val - count.val = b.length
    omega
  have values : window.val = raw.val.slice count.val (count.val + b.length) := by
    simpa only [stopValue] using windowValues
  obtain ⟨restore, rowNormal, rowMeaning⟩ := inner_loop_refines kernels rawMulAgrees
    a[count.val]! window b same 0 (Nat.zero_le _) (fun state => state)
  refine ⟨next, nextValue, ?_⟩
  simp only [mul_into_loop0.body, enumeration, bind_ok]
  dsimp! only
  rw [addNormal]
  simp only [bind_ok, Slice.index_mut_SliceIndexRangeUsizeSliceInst]
  rw [windowNormal]
  simp only [bind_ok, core.slice.Slice.iter_mut]
  dsimp! only
  rw [construct window b]
  simp only [bind_ok]
  dsimp! only
  rw [rowNormal]
  simp only [bind_ok]
  dsimp! only
  rw [rowMeaning]
  simp only [stateAt]
  rw [writeBackExact, restore_row _ _ _ _ _ (by omega) values same]

/-- The original outer loop accumulates all remaining rows into the supplied
scratch buffer. The model keeps the length and retains every slot outside
the shifted row windows. -/
theorem outer_loop_refines : outerLoopFrame := by
  intro K kernels rawMulAgrees a b raw count bounded room
  suffices ∀ remaining (count : Usize) (raw : Slice bulksketch.types.RawProduct),
      count.val ≤ a.length → a.length - count.val = remaining → a.length + b.length ≤ raw.length →
      mul_into_loop0 dictionary kernels (iteratorAt a count) b raw =
        Result.ok (accumulateRows a b raw count.val (a.length - count.val))
    from this (a.length - count.val) count raw bounded rfl room
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro count raw bounded countEq room
    by_cases active : count.val < a.length
    · obtain ⟨next, nextValue, step⟩ := outer_step kernels rawMulAgrees a b raw count active room
      have more : a.length - count.val = (a.length - next.val) + 1 := by omega
      rw [more, accumulateRows, ← nextValue]
      unfold mul_into_loop0 loop
      dsimp only
      rw [step]
      simp only [bind_ok]
      exact ih (a.length - next.val) (by omega) next (row a[count.val]! b raw count.val)
        (by omega) rfl (by simpa using room)
    · have stopped : a.length ≤ count.val := by omega
      rw [Nat.sub_eq_zero_of_le stopped, accumulateRows]
      unfold mul_into_loop0 loop
      dsimp only
      simp only [mul_into_loop0.body, enumerate_done a count stopped, bind_ok]
      dsimp! only
      simp only [bind_ok]

end BulksketchBridge.DenseMulConvolution
