import BulksketchBridge.RootPendingProduct
import BulksketchBridge.RootDivideArena

namespace BulksketchBridge.RootRun

open Aeneas.Std BmEntry DenseCoefficient RebuiltLfsr
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096

def liveDegree (roots : Roots) (stack : Slice FactorFrame) : Nat :=
  roots.degree.val + pendingDegree stack roots.pending.val

theorem live_degree_does_not_grow (roots after : Roots) (stack written : Slice FactorFrame)
    (mass : factorDegreeMass after written = factorDegreeMass roots stack)
    (count : roots.count.val ≤ after.count.val) :
    liveDegree after written ≤ liveDegree roots stack := by
  unfold factorDegreeMass at mass
  unfold liveDegree
  omega

/-- In addition to fitting the allocation, the next coefficient slot
    stays strictly inside the original residual factor's pending region.
    The subspace table begins at stride squared. -/
theorem next_slot_before_affine_table (roots : Roots) (stack : Slice FactorFrame)
    (slots : ∀ slot < roots.pending.val, 0 < slotDegree stack slot)
    (active : 0 < roots.degree.val)
    (stride : liveDegree roots stack < roots.stride.val) :
    roots.pending.val * roots.stride.val + roots.stride.val ≤ roots.stride.val * roots.stride.val := by
  have pending := positive_slots_bound stack roots.pending.val slots
  have next : roots.pending.val + 1 ≤ roots.stride.val := by unfold liveDegree at stride; omega
  calc
    _ = (roots.pending.val + 1) * roots.stride.val := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ next

private theorem suffix_eq_of_words (before after : Slice U64) (offset : Nat)
    (sameLength : after.length = before.length)
    (frame : ∀ i, offset ≤ i → after[i]! = before[i]!) :
    tail after offset = tail before offset := by
  have width : (tail after offset).length = (tail before offset).length := by
    rw [tail_length, tail_length, sameLength]
  apply Slice.ext_getElem width
  intro index inAfter inBefore
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ inAfter, Slice.Inhabited_getElem_eq_getElem! _ _ inBefore]
  have word := frame (offset + index) (by omega)
  simpa only [tail, Slice.getElem!_Nat_eq, Slice.from_val, List.getElem!_eq_getElem?_getD, List.getElem?_drop]
    using word

open RootDivide in
/-- Both the quotient writes and the saved affine base stay inside the
    one committed slot. All words in the separate subspace table are
    unchanged, including for an affine right child resumed later. -/
theorem committed_preserves_affine_table (roots : Roots) (buffers : FactorWork)
    (factors quotient remainder : Slice U64) (stack : Slice FactorFrame) (meter : WorkMeter)
    (length start : Usize) (raw : Slice RawProduct)
    (positive : 0 < roots.stride.val) (lengthRoom : length.val ≤ roots.stride.val)
    (slotRoom : start.val + roots.stride.val ≤ factors.length)
    (beforeTable : start.val + roots.stride.val ≤ roots.stride.val * roots.stride.val) :
    let output := committed roots buffers factors stack meter length start quotient remainder raw
    tail output.2.2.2.2.1 (roots.stride.val * roots.stride.val) =
      tail factors (roots.stride.val * roots.stride.val) := by
  let output := committed roots buffers factors stack meter length start quotient remainder raw
  let words := prefixSlice quotient length.val
  have width : words.length ≤ length.val := by rw [prefix_length]; exact Nat.min_le_left ..
  have factorWidth : output.2.2.2.2.1.length = factors.length := by
    cases affine : roots.affine <;>
      simp only [output, committed, affine, Bool.false_eq_true, ite_true, ite_false, Slice.set_length, Slice.setSlice!_length]
  change tail output.2.2.2.2.1 _ = _
  apply suffix_eq_of_words factors _ _ factorWidth
  intro index outside
  have copied : (factors.setSlice! start.val words.val)[index]! = factors[index]! :=
    Slice.setSlice!_getElem!_suffix _ _ _ _ (by change start.val + words.length ≤ index; omega)
  cases affine : roots.affine
  · simpa only [output, committed, affine, Bool.false_eq_true, ite_false, words] using copied
  · let base := ClosedLeafAdvance.usizeWord (start.val + roots.stride.val - 1)
    have baseValue : base.val = start.val + roots.stride.val - 1 :=
      ClosedLeafAdvance.word_val _ ((Nat.sub_le ..).trans (slotRoom.trans factors.length_ineq))
    simp only [output, committed, affine, ite_true]
    change ((factors.setSlice! start.val words.val).set base _)[index]! = _
    rw [Slice.getElem!_Nat_set_ne _ _ _ _ (by omega)]
    exact copied

#print axioms committed_preserves_affine_table

end BulksketchBridge.RootRun
