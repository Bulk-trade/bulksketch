import BulksketchBridge.RootPendingBudget

namespace BulksketchBridge.RootRun

open Aeneas.Std ClosedLeafAdvance DenseCoefficient SliceKernels Algebra.Gf64 Polynomial
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open scoped BigOperators

noncomputable def pendingAt (workspace : RowWorkspace) (slot : Nat) : Polynomial Field :=
  (workspace.stack.val[slot]?.map (pendingFactor workspace)).getD 1

noncomputable def pendingProduct (workspace : RowWorkspace) (count : Nat) : Polynomial Field :=
  ∏ slot ∈ Finset.range count, pendingAt workspace slot

noncomputable def liveProduct (roots : Roots) (workspace : RowWorkspace) : Polynomial Field :=
  activeFactor roots workspace * pendingProduct workspace roots.pending.val

/-- The exact pop consumes one pending factor and leaves the lower stack
product and all of its coefficient slices intact. -/
theorem popped_pending_product (roots : Roots) (workspace : RowWorkspace) (frame : FactorFrame)
    (bounds : PopBounds roots workspace frame) :
    pendingProduct workspace roots.pending.val =
      liveProduct (poppedRoots roots workspace frame) (poppedWorkspace workspace frame) := by
  have positive : 0 < roots.pending.val := by
    apply Nat.pos_of_ne_zero
    exact fun zero => bounds.1 (UScalar.eq_of_val_eq zero)
  have remaining : (poppedRoots roots workspace frame).pending.val = roots.pending.val - 1 := by
    change (usizeWord (roots.pending.val - 1)).val = _
    exact word_val _ ((Nat.sub_le ..).trans (by scalar_tac))
  have lower (slot : Nat) :
      pendingAt (poppedWorkspace workspace frame) slot = pendingAt workspace slot := by
    unfold pendingAt pendingFactor pendingCoefficients
    rfl
  have same : pendingProduct (poppedWorkspace workspace frame) (roots.pending.val - 1) =
      pendingProduct workspace (roots.pending.val - 1) := by
    unfold pendingProduct
    apply Finset.prod_congr rfl
    intro slot _
    exact lower slot
  unfold liveProduct
  rw [popped_factor roots workspace frame bounds, remaining, same, mul_comm]
  conv_lhs => rw [← Nat.sub_add_cancel positive]
  unfold pendingProduct
  rw [Finset.prod_range_succ]
  simp only [pendingAt, bounds.2.1, Option.map_some, Option.getD_some]

private theorem preserved_region (old written : Slice U64) (start stop cut : Nat)
    (endOld : stop ≤ old.length) (endNew : stop ≤ written.length) (earlier : stop ≤ cut)
    (preserved : ∀ i < cut, written[i]! = old[i]!) :
    ClosedLeaf.region written start stop = ClosedLeaf.region old start stop := by
  have oldWidth := ClosedLeaf.region_length old start stop endOld
  have newWidth := ClosedLeaf.region_length written start stop endNew
  apply Slice.ext_getElem (newWidth.trans oldWidth.symm)
  intro index inWritten inOld
  have inside : index < stop - start := by rwa [newWidth] at inWritten
  have small : start + index < cut := by omega
  have word (words : Slice U64) (fits : stop ≤ words.length) :
      (ClosedLeaf.region words start stop)[index]! = words[start + index]! := by
    simp only [ClosedLeaf.region, Slice.getElem!_Nat_eq, Slice.from_val]
    exact List.getElem!_slice _ _ _ _ ⟨fits, by omega⟩
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ inWritten, Slice.Inhabited_getElem_eq_getElem! _ _ inOld,
    word written endNew, word old endOld, preserved _ small]

/-- The earlier pending factors are unchanged by a commit that writes
after all earlier frames and preserves their stack entries. -/
theorem pending_product_prefix_frame (roots : Roots) (old written : RowWorkspace)
    (layout : PendingLayout roots old.stack old.factors.length old.polynomials.length)
    (width : written.factors.length = old.factors.length)
    (stack : ∀ i < roots.pending.val, written.stack.val[i]? = old.stack.val[i]?)
    (words : ∀ i < roots.pending.val * roots.stride.val, written.factors[i]! = old.factors[i]!) :
    pendingProduct written roots.pending.val = pendingProduct old roots.pending.val := by
  unfold pendingProduct
  apply Finset.prod_congr rfl
  intro slot member
  have live := Finset.mem_range.mp member
  obtain ⟨frame, read, start, _, length, _⟩ := layout.slots slot live
  have regionEnd : frame.coefficient_start.val + frame.coefficient_len.val ≤ roots.pending.val * roots.stride.val := by
    rw [start]
    calc
      _ ≤ slot * roots.stride.val + roots.stride.val := Nat.add_le_add_left length _
      _ = (slot + 1) * roots.stride.val := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ roots.pending.val * roots.stride.val := Nat.mul_le_mul_right _ (by omega)
  have oldRoom := regionEnd.trans layout.factorRoom
  have newRoom : frame.coefficient_start.val + frame.coefficient_len.val ≤ written.factors.length := by rwa [width]
  rw [pendingAt, pendingAt, stack _ live, read]
  simp only [Option.map_some, Option.getD_some, pendingFactor, pendingCoefficients]
  rw [preserved_region _ _ _ _ _ oldRoom newRoom regionEnd words]

private theorem cast_value (word : Usize) : (UScalar.cast .U64 word).val = word.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (word.hBounds.trans_le (Nat.pow_le_pow_right (by decide) System.Platform.numBits_le))

open RootDivide in
/-- The exact committed stack product adds precisely the quotient, with
every earlier factor read from its original unchanged coefficient window. -/
theorem committed_pending_product (roots : Roots) (workspace : RowWorkspace) (buffers : FactorWork)
    (meter : WorkMeter) (length start : Usize) (quotient remainder : Slice U64) (raw : Slice RawProduct)
    (layout : PendingLayout roots workspace.stack workspace.factors.length workspace.polynomials.length)
    (stackRoom : roots.pending.val + 1 ≤ workspace.stack.length)
    (factorRoom : (roots.pending.val + 1) * roots.stride.val ≤ workspace.factors.length)
    (startVal : start.val = roots.pending.val * roots.stride.val)
    (positive : 0 < length.val) (lengthRoom : length.val < roots.stride.val)
    (quotientRoom : length.val ≤ quotient.length) (gcdRoom : roots.gcd_len.val ≤ buffers.gcd.length)
    (modulusRoom : roots.gcd_len.val ≤ buffers.modulus.length) :
    let output := committed roots buffers workspace.factors workspace.stack meter length start quotient remainder raw
    let written := { workspace with factors := output.2.2.2.2.1, stack := output.2.2.2.2.2.1 }
    pendingProduct written output.2.1.pending.val =
      pendingProduct workspace roots.pending.val * slicePolynomial (prefixSlice quotient length.val) ∧
    output.2.1.pending.val = roots.pending.val + 1 ∧
    written.factors.length = workspace.factors.length ∧ written.stack.length = workspace.stack.length ∧
    (∀ slot < roots.pending.val, written.stack.val[slot]? = workspace.stack.val[slot]?) ∧
    ∃ frame, written.stack.val[roots.pending.val]? = some frame ∧
      frame.coefficient_start.val = start.val ∧ frame.coefficient_len.val = length.val := by
  let output := committed roots buffers workspace.factors workspace.stack meter length start quotient remainder raw
  let written := { workspace with factors := output.2.2.2.2.1, stack := output.2.2.2.2.2.1 }
  have pending : output.2.1.pending.val = roots.pending.val + 1 :=
    word_val _ (stackRoom.trans workspace.stack.length_ineq)
  let frame : FactorFrame := ⟨UScalar.cast .U64 start, UScalar.cast .U64 length, directionWord roots, 1#u32⟩
  let saved := if roots.affine then
      { frame with next_direction := UScalar.cast .U32 (usizeWord (roots.affine_rank.val - 1)) }
    else frame
  have stack : written.stack = workspace.stack.set roots.pending saved := by
    cases affine : roots.affine
    · simp only [written, output, committed, saved, affine, Bool.false_eq_true, ite_false, frame]
    · simp only [written, output, committed, saved, affine, ite_true]
      apply Slice.ext
      simp only [Slice.set_val_eq, List.set_set, frame]
  have factors : written.factors.length = workspace.factors.length := by
    cases affine : roots.affine <;>
      simp only [written, output, committed, affine, Bool.false_eq_true, ite_false, ite_true,
        Slice.set_length, Slice.setSlice!_length]
  have earlierStack (slot : Nat) (old : slot < roots.pending.val) :
      written.stack.val[slot]? = workspace.stack.val[slot]? := by
    rw [stack, Slice.set_val_eq, List.getElem?_set_ne (Nat.ne_of_gt old)]
  have current : written.stack.val[roots.pending.val]? = some saved := by
    rw [stack, Slice.set_val_eq, List.getElem?_set_self (by
      change roots.pending.val < workspace.stack.length
      omega)]
  have savedStart : saved.coefficient_start.val = start.val := by
    cases affine : roots.affine <;> simp only [saved, affine, Bool.false_eq_true, ite_false, ite_true, frame, cast_value]
  have savedLength : saved.coefficient_len.val = length.val := by
    cases affine : roots.affine <;> simp only [saved, affine, Bool.false_eq_true, ite_false, ite_true, frame, cast_value]
  have slotEnd : start.val + roots.stride.val ≤ workspace.factors.length := by
    rwa [Nat.add_mul, Nat.one_mul, ← startVal] at factorRoom
  obtain ⟨_, earlierWords⟩ := commit_with_pending_layout roots buffers workspace.factors workspace.stack meter
    length start quotient remainder raw workspace.polynomials.length layout stackRoom factorRoom startVal
    positive lengthRoom.le (fun _ => lengthRoom)
  have preserved : pendingProduct written roots.pending.val = pendingProduct workspace roots.pending.val :=
    pending_product_prefix_frame roots workspace written layout factors earlierStack
      (fun slot old => earlierWords slot (startVal ▸ old))
  obtain ⟨_, quotientWords⟩ := committed_coefficients roots buffers workspace.factors workspace.stack meter
    length start quotient remainder raw positive quotientRoom lengthRoom.le slotEnd (fun _ => lengthRoom) gcdRoom modulusRoom
  have stackWidth : written.stack.length = workspace.stack.length := by rw [stack, Slice.set_length]
  refine ⟨?_, pending, factors, stackWidth, earlierStack, saved, current, savedStart, savedLength⟩
  change pendingProduct written output.2.1.pending.val = _
  rw [pending]
  unfold pendingProduct at preserved ⊢
  rw [Finset.prod_range_succ, preserved, pendingAt, current]
  simp only [Option.map_some, Option.getD_some, pendingFactor, pendingCoefficients, savedStart, savedLength]
  rw [quotientWords]

#print axioms popped_pending_product
#print axioms pending_product_prefix_frame
#print axioms committed_pending_product

end BulksketchBridge.RootRun
