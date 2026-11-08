import Arithmetic.AffineQuarticGenerated

namespace BulksketchBridge.AffineQuarticMin

open Aeneas Aeneas.Std

abbrev KernelWords := Array U64 3#usize

/-- The source chooses the minimum unsigned word from the three kernel roots. -/
def kernelMinimum (roots : KernelWords) : U64 :=
  core.cmp.impls.OrdU64.min (core.cmp.impls.OrdU64.min roots.val[0]! roots.val[1]!) roots.val[2]!

private abbrev sharedOrder := bulksketch.Shared0A.Insts.CoreCmpOrd core.cmp.OrdU64
private abbrev sharedIterator := core.iter.traits.iterator.IteratorSliceIter U64

private theorem shared_min (left right : U64) :
    core.cmp.Ord.min_body (core.cmp.impls.PartialOrdShared.lt core.cmp.PartialOrdU64) left right =
      Result.ok (core.cmp.impls.OrdU64.min left right) := by
  simp [core.cmp.Ord.min_body, core.cmp.impls.PartialOrdShared.lt,
    liftFun2, core.cmp.impls.PartialOrdU64.lt, core.cmp.impls.OrdU64.min, UScalar.lt_equiv]
  split <;> simp_all

private theorem slice_length (roots : KernelWords) : (Array.to_slice roots).length = 3 := by
  rw [Array.length_to_slice]
  rfl

private theorem array_next (roots : KernelWords) (index : Nat) (bounded : index < 3) :
    core.slice.iter.IteratorSliceIter.next ⟨Array.to_slice roots, index⟩ =
      Result.ok (some roots.val[index]!, ⟨Array.to_slice roots, index + 1⟩) := by
  have inside : index < (Array.to_slice roots).len := by
    rw [Slice.len_val, slice_length]
    exact bounded
  rw [core.slice.iter.IteratorSliceIter.next, dite_eq_left inside]
  apply congrArg (fun word => Result.ok (some word,
    (⟨Array.to_slice roots, index + 1⟩ : core.slice.iter.Iter U64)))
  have valid : index < (Array.to_slice roots).length := by rwa [slice_length]
  change (Array.to_slice roots)[index]'valid = roots.val[index]!
  rw [Slice.Inhabited_getElem_eq_getElem! _ index valid, Slice.getElem!_Nat_eq, Array.val_to_slice]

private theorem array_end (roots : KernelWords) :
    core.slice.iter.IteratorSliceIter.next ⟨Array.to_slice roots, 3⟩ =
      Result.ok (none, ⟨Array.to_slice roots, 3⟩) := by
  have exhausted : ¬(3 : Nat) < (Array.to_slice roots).len := by
    rw [Slice.len_val, slice_length]
    exact Nat.lt_irrefl _
  rw [core.slice.iter.IteratorSliceIter.next, dite_eq_right exhausted]

private theorem minimum_step (roots : KernelWords) (index : Nat) (bounded : index < 3)
    (least : U64) :
    AffineQuarticRuntime.minimumStep sharedIterator sharedOrder (⟨Array.to_slice roots, index⟩, least) =
      Result.ok (.cont (⟨Array.to_slice roots, index + 1⟩, core.cmp.impls.OrdU64.min least roots.val[index]!)) := by
  simp only [AffineQuarticRuntime.minimumStep, array_next roots index bounded, bind_ok]
  dsimp! only
  simp only [shared_min, bind_ok]

private theorem minimum_end (roots : KernelWords) (least : U64) :
    AffineQuarticRuntime.minimumStep sharedIterator sharedOrder (⟨Array.to_slice roots, 3⟩, least) =
      Result.ok (.done least) := by
  simp [AffineQuarticRuntime.minimumStep, array_end, bind_ok]

/-- The actual three-word iterator reads each kernel word and makes two
unsigned minimum selections. -/
theorem kernel_minimum_refines (roots : KernelWords) :
    AffineQuarticRuntime.minimum (core.iter.traits.iterator.IteratorSliceIter U64)
      (bulksketch.Shared0A.Insts.CoreCmpOrd core.cmp.OrdU64) ⟨Array.to_slice roots, 0⟩ =
        Result.ok (some (kernelMinimum roots)) := by
  have fold : loop (AffineQuarticRuntime.minimumStep sharedIterator sharedOrder)
      (⟨Array.to_slice roots, 1⟩, roots.val[0]!) = Result.ok (kernelMinimum roots) := by
    rw [loop]
    simp only [minimum_step roots 1 (by decide), bind_ok]
    rw [loop]
    simp only [minimum_step roots 2 (by decide), bind_ok]
    change loop (AffineQuarticRuntime.minimumStep sharedIterator sharedOrder)
      (⟨Array.to_slice roots, 3⟩, kernelMinimum roots) = _
    rw [loop]
    simp only [minimum_end, bind_ok, kernelMinimum]
  simp only [AffineQuarticRuntime.minimum, array_next roots 0 (by decide), bind_ok]
  dsimp! only
  simp only [fold, bind_ok]

private theorem kernel_word_mem (roots : KernelWords) (index : Nat) (bounded : index < 3) :
    roots.val[index]! ∈ roots.val := by
  have inside : index < roots.val.length := by
    rw [Array.property]
    exact bounded
  rw [← List.Inhabited_getElem_eq_getElem! _ _ inside]
  exact List.getElem_mem _

theorem kernelMinimum_mem (roots : KernelWords) : kernelMinimum roots ∈ roots.val := by
  have select (left right : U64) (leftMem : left ∈ roots.val) (rightMem : right ∈ roots.val) :
      core.cmp.impls.OrdU64.min left right ∈ roots.val := by
    unfold core.cmp.impls.OrdU64.min
    split
    · exact rightMem
    · exact leftMem
  exact select _ _ (select _ _ (kernel_word_mem roots 0 (by decide))
    (kernel_word_mem roots 1 (by decide))) (kernel_word_mem roots 2 (by decide))

theorem kernelMinimum_le (roots : KernelWords) (index : Nat) (bounded : index < 3) :
    (kernelMinimum roots).val ≤ (roots.val[index]!).val := by
  simp only [kernelMinimum, core.cmp.impls.OrdU64.min_val]
  have indices : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases indices with rfl | rfl | rfl
  · exact (Nat.min_le_left _ _).trans (Nat.min_le_left _ _)
  · exact (Nat.min_le_left _ _).trans (Nat.min_le_right _ _)
  · exact Nat.min_le_right _ _

end BulksketchBridge.AffineQuarticMin
