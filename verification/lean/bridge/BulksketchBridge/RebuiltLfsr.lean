import BulksketchBridge.RebuiltSquareLoop

namespace BulksketchBridge.RebuiltLfsr

open Aeneas Aeneas.Std Aeneas.Std.WP DenseCoefficient
open bulksketch.decode.verify

theorem inclusive_prefix (words : Slice U64) (last : Usize) (bound : last.val < words.length) :
    (RebuiltLfsrRuntime.inclusive U64).index_mut ⟨last⟩ words =
      Result.ok (prefixSlice words (last.val + 1), restorePrefix words) := by
  have sizeBound : words.length ≤ Usize.max := words.length_ineq
  obtain ⟨stop, addNormal, addValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := last) (y := 1#usize) (by change last.val + 1 ≤ Usize.max; omega))
  have exactStop : stop.val = last.val + 1 := addValue
  have sliced := prefix_normal words stop (by omega)
  simp only [RebuiltLfsrRuntime.inclusive, bound, ite_true, addNormal, bind_ok, sliced, exactStop]

private theorem seed_ne (left right : Slice U64) :
    RebuiltLfsrRuntime.mutableSharedNe
      (bulksketch.Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU64) left right =
      Result.ok (decide (left ≠ right)) := by
  have proof := core.cmp.PartialEq.ne.trait_default.spec
    (bulksketch.Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU64) left right (by
      apply core.slice.cmp.PartialEqSlice.eq_homo_spec
      intro x y
      change WP.spec (Result.ok (decide (x ≠ y))) _
      simp only [spec_ok, decide_eq_true_eq])
  obtain ⟨result, normal, meaning⟩ := RawMulTable.normal_of_spec _ _ proof
  have exactResult : result = decide (left ≠ right) := by
    apply Bool.eq_iff_iff.mpr
    simpa using meaning
  rw [RebuiltLfsrRuntime.mutableSharedNe]
  change core.cmp.PartialEq.ne.default (core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU64) left right = _
  exact normal.trans (congrArg Result.ok exactResult)

private theorem square_restored (words tail : Slice U64) (back : Slice U64 → Slice U64)
    (nonempty : 0 < words.length) (tailValues : tail.val = words.val.drop 1)
    (tailLength : tail.length = words.length - 1)
    (writeBack : ∀ replacement, (back replacement).val = words.val.setSlice! 1 replacement.val) :
    back (squareFrom tail 0) = squareFrom words 1 := by
  have lengthBack : (back (squareFrom tail 0)).length = words.length := by
    change (back (squareFrom tail 0)).val.length = words.val.length
    simp only [writeBack, List.length_setSlice!]
  apply Slice.ext_getElem (lengthBack.trans (square_length words 1).symm)
  intro index backBound squaredBound
  have inside : index < words.length := by simpa using squaredBound
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ backBound,
    Slice.Inhabited_getElem_eq_getElem! _ _ squaredBound,
    square_word words 1 index inside, Slice.getElem!_Nat_eq, writeBack]
  by_cases first : index = 0
  · subst index
    rw [List.getElem!_setSlice!_prefix _ _ _ _ (by decide), ite_eq_right (by decide)]
    exact (Slice.getElem!_Nat_eq words 0).symm
  · have tailBound : index - 1 < tail.length := by omega
    rw [List.getElem!_setSlice!_middle _ _ _ _ (by
      rw [show (squareFrom tail 0).val.length = tail.length from square_length tail 0]
      exact ⟨by omega, tailBound, inside⟩), ← Slice.getElem!_Nat_eq,
      square_word tail 0 _ tailBound, ite_eq_left (Nat.zero_le _), ite_eq_left (by omega)]
    congr 1
    rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_eq, tailValues,
      List.getElem!_eq_getElem?_getD, List.getElem?_drop, show 1 + (index - 1) = index by omega]
    exact List.getElem!_eq_getElem?_getD.symm

theorem rebuilt_lfsr_refines : ActualRebuiltLfsrReturnsFrames := by
  intro K kernels linear square roots odd coefficients expected seed room expectedRoom seedLen insert
  dsimp only
  intro continuation
  let locatorShape := prefixSlice coefficients (roots.length + 1)
  let initial := (zeroWords locatorShape).setAtNat 0 1#u64
  let locator := locatorWords roots locatorShape
  have shapeLen : locatorShape.length = roots.length + 1 := by simp [locatorShape, Nat.min_eq_left (by omega : roots.length + 1 ≤ coefficients.length)]
  have initLen : initial.length = roots.length + 1 := by simp [initial, Slice.setAtNat_length, shapeLen]
  have locatorLen : locator.length = roots.length + 1 := by simp [locator, locatorWords, ← initLen, initial]
  have included : core.slice.index.Slice.index_mut (RebuiltLfsrRuntime.inclusive U64)
      coefficients ⟨roots.len⟩ = Result.ok (locatorShape, restorePrefix coefficients) := by
    simpa only [core.slice.index.Slice.index_mut, locatorShape, Slice.len_val] using inclusive_prefix coefficients roots.len (by simpa using room)
  obtain ⟨initialized, updateNormal, updateValue⟩ := RawMulTable.normal_of_spec _ _
    (Slice.update_spec (zeroWords locatorShape) 0#usize 1#u64 (by simp [shapeLen]))
  have initializedEq : initialized = initial := updateValue
  have iterated := locator_loop kernels linear roots initial 0#usize roots.length
    (by simp) (by omega)
  let stop := core.cmp.impls.OrdUsize.min roots.len odd.len
  have stopVal : stop.val = seed.length := by
    unfold stop core.cmp.impls.OrdUsize.min
    split <;> rename_i order
    · have smaller : odd.length ≤ roots.length := by
        have : odd.len.val < roots.len.val := (UScalar.lt_equiv _ _).mp order
        simpa using this.le
      simpa [Nat.min_eq_right smaller] using seedLen.symm
    · have smaller : roots.length ≤ odd.length := by
        have : ¬ odd.len.val < roots.len.val := fun lt => order ((UScalar.lt_equiv _ _).mpr lt)
        simpa using Nat.le_of_not_gt this
      simpa [Nat.min_eq_left smaller] using seedLen.symm
  have expectedCut : core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice U64) expected
        ⟨core.cmp.impls.OrdUsize.min roots.len odd.len⟩ =
      Result.ok (prefixSlice expected seed.length, restorePrefix expected) := by
    have cut := prefix_normal expected stop (by omega)
    rw [stopVal] at cut
    exact cut
  have oddCut : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeToUsizeSlice U64) odd
        ⟨core.cmp.impls.OrdUsize.min roots.len odd.len⟩ =
      Result.ok (prefixSlice odd seed.length) := by
    have cut := shared_prefix_normal odd stop (by omega)
    rw [stopVal] at cut
    exact cut
  have compared := seed_ne seed (prefixSlice odd seed.length)
  have start :=
    show core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter U64) (⟨roots, 0⟩ : core.slice.iter.Iter U64) =
      Result.ok (⟨⟨roots, 0⟩, 0#usize⟩ : RootIterator) from rfl
  have locatorStepResult :
      rebuilt_lfsr_loop0 kernels ⟨⟨roots, 0⟩, 0#usize⟩ initial = Result.ok locator := by
    simpa only [locator, locatorWords, initial, show (0#usize : Usize).val = 0 by simp] using iterated
  by_cases equal : seed = prefixSlice odd seed.length
  · obtain ⟨result, recurrence⟩ := continuation equal
    refine ⟨result, ?_, ?_⟩
    · have positive : 0 < locator.length := by omega
      have notDifferent : decide (seed ≠ prefixSlice odd seed.length) = false := by
        exact decide_eq_false (fun diff => diff equal)
      obtain ⟨⟨tail, back⟩, tailNormal, tailValues, tailLen, writeBack⟩ := RawMulTable.normal_of_spec _ _
        (core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut.step_spec
          ⟨1#usize⟩ locator (by simpa using Nat.succ_le_of_lt positive))
      have exactLength : tail.length = locator.length - 1 := by simpa using tailLen
      have exactValues : tail.val = locator.val.drop 1 := by simpa using tailValues
      obtain ⟨finish, scan, returned⟩ := square_loop kernels square tail 0 tail.length (by simp) id
      have scanExact : rebuilt_lfsr_loop1 bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels
          ⟨tail, 0⟩ (fun state => state) = Result.ok (⟨tail, tail.length⟩, finish) := scan
      have restored := square_restored locator tail back positive exactValues exactLength writeBack
      rw [ite_eq_left equal]
      simp only [rebuilt_lfsr, lift, bind_ok, included]
      try dsimp! only
      simp only [fill_zero, updateNormal, initializedEq, bind_ok, core.slice.Slice.iter,
        start, locatorStepResult, expectedCut, bind_ok]
      try dsimp! only
      simp only [insert, bind_ok,
        oddCut, compared, notDifferent, Bool.false_eq_true, ite_false]
      simp only [Slice.index_mut_SliceIndexRangeFromUsizeSliceInst, tailNormal, bind_ok]
      try dsimp! only
      simp only [RebuiltLfsrRuntime.mutableIntoIter, core.slice.Slice.iter_mut, bind_ok]
      try dsimp! only
      rw [scanExact]
      try dsimp! only
      simp only [bind_ok]
      dsimp! only
      have recurrenceExact : kernels.odd_recurrence_matches odd (squareFrom locator 1) = Result.ok result :=
        recurrence
      simp only [show finish ⟨tail, tail.length⟩ = ⟨squareFrom tail 0, tail.length⟩ from returned,
        restored, recurrenceExact, bind_ok]
      rfl
    · rw [ite_eq_left equal]
      exact recurrence
  · refine ⟨false, ?_, ?_⟩
    · have different : decide (seed ≠ prefixSlice odd seed.length) = true := decide_eq_true equal
      rw [ite_eq_right equal]
      simp only [rebuilt_lfsr, lift, bind_ok, included]
      try dsimp! only
      simp only [fill_zero, updateNormal, initializedEq, bind_ok, core.slice.Slice.iter,
        start, locatorStepResult, expectedCut, bind_ok]
      try dsimp! only
      simp only [insert, bind_ok,
        oddCut, compared, different, ite_true]
      rfl
    · rw [ite_eq_right equal]

end BulksketchBridge.RebuiltLfsr
