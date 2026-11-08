import BulksketchBridge.RebuiltLocatorLoop

namespace BulksketchBridge.ClosedLeaf

open Aeneas Aeneas.Std Aeneas.Std.WP DenseCoefficient RebuiltLfsr

def region (words : Slice U64) (start stop : Nat) : Slice U64 :=
  Slice.from (words.val.slice start stop)
    (Nat.le_trans (List.slice_length_le start stop words.val) (Slice.length_ineq words))

@[simp] theorem region_length (words : Slice U64) (start stop : Nat)
    (bounded : stop ≤ words.length) : (region words start stop).length = stop - start := by
  simp only [region, Slice.length, Slice.from_val, List.slice_length]
  apply Nat.min_eq_right
  exact Nat.sub_le_sub_right bounded start

theorem region_prefix (words : Slice U64) (n start stop : Nat) (bounded : stop ≤ n) :
    region (prefixSlice words n) start stop = region words start stop := by
  apply Slice.ext
  simp only [region, prefixSlice, Slice.from_val, List.slice, List.drop_take, List.take_take]
  rw [Nat.min_eq_left (by omega)]

theorem prefix_prefix (words : Slice U64) (n stop : Nat) (bounded : stop ≤ n) :
    prefixSlice (prefixSlice words n) stop = prefixSlice words stop := by
  apply Slice.ext
  simp [prefixSlice, List.take_take, Nat.min_eq_left bounded]

theorem shared_region_normal (words : Slice U64) (start stop : Usize)
    (ordered : start.val ≤ stop.val) (bounded : stop.val ≤ words.length) :
    core.slice.index.SliceIndexRangeUsizeSlice.index ⟨start, stop⟩ words =
      Result.ok (region words start.val stop.val) := by
  have h0 : start ≤ stop := by scalar_tac
  have h1 : stop ≤ words.length := bounded
  obtain ⟨window, normal, payload, _⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec ⟨start, stop⟩ words h0 h1)
  rw [normal]
  exact congrArg Result.ok (Slice.ext _ _ (by simpa only [region, Slice.from_val] using payload))

theorem mutable_region_normal (words : Slice U64) (start stop : Usize)
    (ordered : start.val ≤ stop.val) (bounded : stop.val ≤ words.length) :
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut ⟨start, stop⟩ words =
      Result.ok (region words start.val stop.val, fun replacement => words.setSlice! start.val replacement.val) := by
  have h0 : start ≤ stop := by scalar_tac
  have h1 : stop ≤ words.length := bounded
  obtain ⟨⟨window, back⟩, normal, payload, _, backEq⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec ⟨start, stop⟩ words h0 h1)
  rw [normal, show window = region words start.val stop.val from Slice.ext _ _ (by simpa only [region, Slice.from_val] using payload), funext backEq]

theorem inclusive_prefix_normal (words : Slice U64) (last : Usize)
    (bounded : last.val < words.length) :
    (Aeneas.Std.RebuiltLfsrRuntime.inclusive U64).index ⟨last⟩ words =
      Result.ok (prefixSlice words (last.val + 1)) := by
  have fits : last.val + (1#usize).val ≤ Usize.max := by
    have length := Slice.length_ineq words
    change words.length ≤ Usize.max at length
    change last.val + 1 ≤ Usize.max
    omega
  obtain ⟨stop, normal, value⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := last) (y := 1#usize) fits)
  have stopEq : stop.val = last.val + 1 := value
  simp only [RebuiltLfsrRuntime.inclusive, bounded, ite_true, normal, bind_ok,
    shared_prefix_normal words stop (by omega), stopEq]

theorem copy_normal (destination source : Slice U64) (length : destination.length = source.length) :
    core.slice.Slice.copy_from_slice core.marker.CopyU64 destination source = .ok source := by
  obtain ⟨copied, normal, words⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.Slice.copy_from_slice.step_spec core.marker.CopyU64 destination source length)
  rw [normal, words]

theorem split_normal (words : Slice U64) (split : Usize) (bounded : split.val ≤ words.length) :
    ∃ tail back,
      core.slice.Slice.split_at_mut words split = .ok ((prefixSlice words split.val, tail), back) ∧
      tail.val = words.val.drop split.val ∧ tail.length = words.length - split.val ∧
      ∀ replacement : Slice U64, replacement.length ≤ tail.length →
        back (prefixSlice words split.val, restorePrefix tail replacement) =
          words.setSlice! split.val replacement.val := by
  obtain ⟨⟨⟨head, tail⟩, back⟩, normal, headLen, tailLen, headVal, tailVal, restore⟩ :=
    RawMulTable.normal_of_spec _ _ (core.slice.Slice.split_at_mut.spec words split bounded)
  change tail.length = words.length - split.val at tailLen
  have headEq : head = prefixSlice words split.val := Slice.ext _ _ (by simpa only [prefixSlice, Slice.from_val] using headVal)
  subst head
  refine ⟨tail, back, normal, tailVal, tailLen, ?_⟩
  intro replacement room
  apply Slice.ext
  rw [(restore _ _ headLen (by rw [restore_length, tailLen])).1]
  have tailRoom : replacement.val.length ≤ words.val.length - split.val := by
    change replacement.length ≤ words.length - split.val
    omega
  simp only [prefixSlice, restorePrefix, Slice.from_val, Slice.setSlice!_val, tailVal, List.setSlice!,
    List.take_zero, List.nil_append, List.length_drop, Nat.sub_zero, Nat.min_eq_left tailRoom, List.take_length,
    Nat.zero_add, List.drop_drop, Nat.add_comm, List.append_assoc]

theorem overwrite_original_region (words : Slice U64) (start count : Nat)
    (bounded : start + count ≤ words.length) :
    words.setSlice! start (region words start (start + count)).val = words := by
  apply Slice.ext
  have remaining : count ≤ words.val.length - start := by
    change count ≤ words.length - start
    omega
  have length : (region words start (start + count)).val.length = count := by
    change (region words start (start + count)).length = count
    rw [region_length words start (start + count) bounded]
    omega
  rw [Slice.setSlice!_val, List.setSlice!, length, Nat.min_eq_left remaining]
  have payload : (region words start (start + count)).val.take count =
      (region words start (start + count)).val := by
    nth_rw 1 [← length]
    exact List.take_length
  rw [payload]
  simp only [region, Slice.from_val, List.slice, Nat.add_sub_cancel_left]
  rw [List.append_assoc, ← List.drop_drop,
    List.take_append_drop, List.take_append_drop]

theorem prefix_tail_region (words tail : Slice U64) (start count : Nat)
    (tailVal : tail.val = words.val.drop start) :
    prefixSlice tail count = region words start (start + count) := by
  apply Slice.ext
  simp [prefixSlice, region, List.slice, tailVal]

end BulksketchBridge.ClosedLeaf
