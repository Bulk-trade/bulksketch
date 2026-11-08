import BulksketchBridge.RebuiltLfsrSpec

namespace BulksketchBridge.RebuiltLfsr

open Aeneas Aeneas.Std Aeneas.Std.WP DenseCoefficient
open bulksketch.decode.verify

@[simp] theorem prefix_length (words : Slice U64) (count : Nat) :
    (prefixSlice words count).length = min count words.length := by
  simp [prefixSlice, Slice.length]

@[simp] theorem restore_length (words replacement : Slice U64) :
    (restorePrefix words replacement).length = words.length := by
  simp [restorePrefix, Slice.length]

@[simp] theorem linear_length (words : Slice U64) (root : U64) :
    (linearStep words root).length = words.length := by simp [linearStep, Slice.length]

@[simp] theorem locator_step_length (words : Slice U64) (root : U64) (stop : Nat) :
    (locatorStep words root stop).length = words.length := by simp [locatorStep]

@[simp] theorem zero_length (shape : Slice U64) : (zeroWords shape).length = shape.length := by
  simp [zeroWords, Slice.length]

@[simp] theorem locator_length (roots current : Slice U64) (index count : Nat) :
    (locatorFrom roots current index count).length = current.length := by
  induction count generalizing current index with
  | zero => rfl
  | succ count ih => simp [locatorFrom, ih]

theorem prefix_normal (words : Slice U64) (stop : Usize) (bound : stop.val ≤ words.length) :
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut ⟨stop⟩ words =
      Result.ok (prefixSlice words stop.val, restorePrefix words) := by
  obtain ⟨⟨window, back⟩, result, exactWindow, _, exactBack⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeToUsizeSlice.index_mut.step_spec ⟨stop⟩ words bound)
  have windowEq : window = prefixSlice words stop.val := by
    rw [Slice.eq_iff]
    simpa [prefixSlice, List.slice_zero_j] using exactWindow
  have backEq : back = restorePrefix words := by
    funext replacement
    rw [Slice.eq_iff]
    simpa only [restorePrefix, Slice.from_val] using exactBack replacement
  rw [result, windowEq, backEq]

theorem shared_prefix_normal (words : Slice U64) (stop : Usize) (bound : stop.val ≤ words.length) :
    core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨stop⟩ words =
      Result.ok (prefixSlice words stop.val) := by
  obtain ⟨window, result, exactWindow, _⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec ⟨stop⟩ words bound)
  have windowEq : window = prefixSlice words stop.val := by
    rw [Slice.eq_iff]
    simpa [prefixSlice, List.slice_zero_j] using exactWindow
  rw [result, windowEq]

theorem fill_zero (shape : Slice U64) :
    core.slice.Slice.fill core.clone.CloneU64 shape 0#u64 = Result.ok (zeroWords shape) := by
  obtain ⟨zeros, result, length, values⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.Slice.fill.spec core.clone.CloneU64 shape 0#u64
      (by exact (WP.spec_ok (0#u64)).mpr rfl))
  have equal : zeros = zeroWords shape := by
    rw [Slice.eq_iff]
    simpa [zeroWords, length] using values
  rw [result, equal]

abbrev RootIterator := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U64)

theorem root_next (roots : Slice U64) (index : Usize) (active : index.val < roots.length) :
    ∃ next : Usize,
      core.iter.adapters.enumerate.IteratorEnumerate.next (core.iter.traits.iterator.IteratorSliceIter U64)
          (⟨⟨roots, index.val⟩, index⟩ : RootIterator) =
        Result.ok (some (index, roots[index.val]!), (⟨⟨roots, next.val⟩, next⟩ : RootIterator)) ∧
      next.val = index.val + 1 := by
  have shared : core.slice.iter.IteratorSliceIter.next (⟨roots, index.val⟩ : core.slice.iter.Iter U64) =
      Result.ok (some roots[index.val]!, ⟨roots, index.val + 1⟩) := by
    unfold core.slice.iter.IteratorSliceIter.next
    split
    · apply congrArg (fun value => Result.ok (some value, (⟨roots, index.val + 1⟩ : core.slice.iter.Iter U64)))
      with_unfolding_all exact Slice.Inhabited_getElem_eq_getElem! roots index.val active
    · rename_i exhausted
      exact False.elim (exhausted (by simpa using active))
  have step := core.iter.adapters.enumerate.IteratorEnumerate.next_some_spec
    (core.iter.traits.iterator.IteratorSliceIter U64) (⟨⟨roots, index.val⟩, index⟩ : RootIterator)
    roots[index.val]! ⟨roots, index.val + 1⟩ (by
      change WP.spec (core.slice.iter.IteratorSliceIter.next _) _
      rw [shared]; simp only [spec_ok, and_self]) (by
      have maxBound : roots.length ≤ Usize.max := roots.length_ineq
      change index.val + 1 ≤ Usize.max
      omega)
  obtain ⟨⟨opt, state⟩, normal, rfl, inner, count⟩ := RawMulTable.normal_of_spec _ _ step
  refine ⟨state.count, ?_, count⟩
  have exactState : state = ⟨⟨roots, state.count.val⟩, state.count⟩ := by
    cases state
    simp_all
  rw [normal]
  conv => lhs; rw [exactState]

theorem root_done (roots : Slice U64) (index : Usize) (stop : index.val = roots.length) :
    ∃ terminal : RootIterator,
      core.iter.adapters.enumerate.IteratorEnumerate.next (core.iter.traits.iterator.IteratorSliceIter U64)
          (⟨⟨roots, index.val⟩, index⟩ : RootIterator) = Result.ok (none, terminal) := by
  have shared : core.slice.iter.IteratorSliceIter.next (⟨roots, index.val⟩ : core.slice.iter.Iter U64) =
      Result.ok (none, ⟨roots, index.val⟩) := by
    unfold core.slice.iter.IteratorSliceIter.next
    have done : ¬ index.val < roots.len.val := by simp [stop]
    rw [dite_eq_right done]
  have step := core.iter.adapters.enumerate.IteratorEnumerate.next_none_spec
    (core.iter.traits.iterator.IteratorSliceIter U64) (⟨⟨roots, index.val⟩, index⟩ : RootIterator)
    ⟨roots, index.val⟩ (by
      change WP.spec (core.slice.iter.IteratorSliceIter.next _) _
      rw [shared]; simp only [spec_ok, and_self])
  obtain ⟨⟨opt, state⟩, normal, rfl, _, _⟩ := RawMulTable.normal_of_spec _ _ step
  exact ⟨state, normal⟩

theorem locator_loop {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (linear : linearLaw kernels) (roots current : Slice U64)
    (index : Usize) (count : Nat) (remaining : index.val + count = roots.length)
    (room : roots.length < current.length) :
    rebuilt_lfsr_loop0 kernels (⟨⟨roots, index.val⟩, index⟩ : RootIterator) current =
      Result.ok (locatorFrom roots current index.val count) := by
  induction count generalizing index current with
  | zero =>
    obtain ⟨terminal, stop⟩ := root_done roots index (by omega)
    unfold rebuilt_lfsr_loop0 loop
    dsimp only
    simp only [rebuilt_lfsr_loop0.body, stop, bind_ok]
    dsimp! only
    simp only [bind_ok]
  | succ count ih =>
    obtain ⟨next, read, advanced⟩ := root_next roots index (by omega)
    obtain ⟨stop, plusTwo, stopVal⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := index) (y := 2#usize) (by
        have maxBound : current.length ≤ Usize.max := current.length_ineq
        change index.val + 2 ≤ Usize.max
        omega))
    have endVal : stop.val = index.val + 2 := stopVal
    have cut := prefix_normal current stop (by omega)
    have rest := ih (locatorStep current roots[index.val]! (index.val + 2)) next
      (by omega) (by simpa using room)
    unfold rebuilt_lfsr_loop0 loop
    dsimp only
    simp only [rebuilt_lfsr_loop0.body, read, bind_ok]
    dsimp! only
    simp only [plusTwo, Slice.index_mut_SliceIndexRangeToUsizeSliceInst, cut, bind_ok]
    dsimp! only
    have applyLinear := linear (prefixSlice current (index.val + 2)) roots[index.val]!
    simp only [endVal, applyLinear, bind_ok]
    change rebuilt_lfsr_loop0 kernels (⟨⟨roots, next.val⟩, next⟩ : RootIterator)
      (locatorStep current roots[index.val]! (index.val + 2)) = _
    rw [rest, advanced]

end BulksketchBridge.RebuiltLfsr
