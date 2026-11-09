import BulksketchBridge.ClosedLeafAdvance
import BulksketchBridge.RootDivideNative

namespace BulksketchBridge.RootRun

open Aeneas.Std ClosedLeafAdvance RebuiltLfsr
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- A live stack slot owns its fixed-stride factor region. Affine frames
    reserve the last word of that region for the saved base. -/
def SlotLayout (roots : Roots) (slot : Nat) (frame : FactorFrame) : Prop :=
  frame.coefficient_start.val = slot * roots.stride.val ∧
  1 ≤ frame.coefficient_len.val ∧ frame.coefficient_len.val ≤ roots.stride.val ∧
  (roots.affine = true → frame.coefficient_len.val < roots.stride.val)

structure PendingLayout (roots : Roots) (stack : Slice FactorFrame) (factorWords polynomialWords : Nat) : Prop where
  stackRoom : roots.pending.val ≤ stack.length
  factorRoom : roots.pending.val * roots.stride.val ≤ factorWords
  polynomialRoom : roots.stride.val ≤ polynomialWords
  slots : ∀ slot < roots.pending.val, ∃ frame, stack.val[slot]? = some frame ∧ SlotLayout roots slot frame

theorem empty_pending_layout (roots : Roots) (workspace : RowWorkspace)
    (empty : roots.pending = 0#usize) (strideRoom : roots.stride.val ≤ workspace.polynomials.length) :
    PendingLayout roots workspace.stack workspace.factors.length workspace.polynomials.length := by
  refine ⟨?_, ?_, strideRoom, ?_⟩
  · rw [empty]
    exact Nat.zero_le _
  · simp only [empty, show (0#usize).val = 0 from rfl, Nat.zero_mul, Nat.zero_le]
  · intro slot live
    rw [empty] at live
    exact (Nat.not_lt_zero _ live).elim

theorem pop_bounds_of_pending_layout (roots : Roots) (workspace : RowWorkspace)
    (layout : PendingLayout roots workspace.stack workspace.factors.length workspace.polynomials.length)
    (active : roots.pending ≠ 0#usize) :
    ∃ frame, PopBounds roots workspace frame ∧ SlotLayout roots (roots.pending.val - 1) frame := by
  have positive : 0 < roots.pending.val := by
    apply Nat.pos_of_ne_zero
    intro empty
    apply active
    exact UScalar.eq_of_val_eq empty
  obtain ⟨frame, present, start, nonempty, width, affineWidth⟩ := layout.slots (roots.pending.val - 1) (by omega)
  have endOfSlot : frame.coefficient_start.val + roots.stride.val = roots.pending.val * roots.stride.val := by
    rw [start]
    calc
      _ = (roots.pending.val - 1 + 1) * roots.stride.val := by rw [Nat.add_mul, Nat.one_mul]
      _ = _ := by rw [Nat.sub_add_cancel positive]
  refine ⟨frame, ⟨active, present, nonempty, width.trans layout.polynomialRoom, ?_, ?_⟩,
    start, nonempty, width, affineWidth⟩
  · exact (Nat.add_le_add_left width _).trans (endOfSlot ▸ layout.factorRoom)
  · intro _
    constructor
    · omega
    · rw [endOfSlot]
      exact layout.factorRoom

theorem popped_pending_layout (roots : Roots) (workspace : RowWorkspace) (frame : FactorFrame)
    (layout : PendingLayout roots workspace.stack workspace.factors.length workspace.polynomials.length) :
    PendingLayout (poppedRoots roots workspace frame) (poppedWorkspace workspace frame).stack
      (poppedWorkspace workspace frame).factors.length (poppedWorkspace workspace frame).polynomials.length := by
  have count : (poppedRoots roots workspace frame).pending.val = roots.pending.val - 1 := by
    change (usizeWord (roots.pending.val - 1)).val = _
    exact word_val _ ((Nat.sub_le ..).trans (by scalar_tac))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [count]
    exact (Nat.sub_le ..).trans layout.stackRoom
  · rw [count]
    exact (Nat.mul_le_mul_right _ (Nat.sub_le ..)).trans layout.factorRoom
  · simpa only [poppedRoots, poppedWorkspace, restore_length] using layout.polynomialRoom
  · intro slot live
    rw [count] at live
    obtain ⟨stored, read, valid⟩ := layout.slots slot (by omega)
    exact ⟨stored, read, valid⟩

/-- The original pop is admitted by the live stack layout. It preserves
    the remaining frames and performs the exact modeled workspace write. -/
def ActualAdvanceWithPendingLayout : Prop :=
  ∀ (roots : Roots) (workspace : RowWorkspace),
    PendingLayout roots workspace.stack workspace.factors.length workspace.polynomials.length →
    if roots.pending = 0#usize then
      Roots.advance roots workspace = .ok (.Verification, roots, workspace, id)
    else
      ∃ frame, PopBounds roots workspace frame ∧
        let after := poppedRoots roots workspace frame
        let written := poppedWorkspace workspace frame
        Roots.advance roots workspace = .ok (stageFor after, after, written, id) ∧
          PendingLayout after written.stack written.factors.length written.polynomials.length

theorem advance_with_pending_layout : ActualAdvanceWithPendingLayout := by
  intro roots workspace layout
  by_cases empty : roots.pending = 0#usize
  · rw [ite_eq_left empty]
    exact advance_empty_refines roots workspace empty
  · rw [ite_eq_right empty]
    obtain ⟨frame, bounds, _⟩ := pop_bounds_of_pending_layout roots workspace layout empty
    exact ⟨frame, bounds, advance_pop_refines roots workspace frame bounds,
      popped_pending_layout roots workspace frame layout⟩

private theorem pushed_slots (roots after : Roots) (stack : Slice FactorFrame)
    (factorWords polynomialWords : Nat) (frame : FactorFrame)
    (layout : PendingLayout roots stack factorWords polynomialWords)
    (stackRoom : roots.pending.val + 1 ≤ stack.length)
    (factorRoom : (roots.pending.val + 1) * roots.stride.val ≤ factorWords)
    (newSlot : SlotLayout roots roots.pending.val frame)
    (count : after.pending.val = roots.pending.val + 1)
    (stride : after.stride = roots.stride) (affine : after.affine = roots.affine) :
    PendingLayout after (stack.set roots.pending frame) factorWords polynomialWords := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [count, Slice.set_length] using stackRoom
  · simpa only [count, stride] using factorRoom
  · simpa only [stride] using layout.polynomialRoom
  · intro slot live
    rw [count] at live
    by_cases newest : slot = roots.pending.val
    · subst slot
      refine ⟨frame, ?_, by simpa only [SlotLayout, stride, affine] using newSlot⟩
      rw [Slice.set_val_eq]
      exact List.getElem?_set_self (by change roots.pending.val < stack.length; omega)
    · obtain ⟨old, read, shape⟩ := layout.slots slot (by omega)
      refine ⟨old, ?_, by simpa only [SlotLayout, stride, affine] using shape⟩
      rw [Slice.set_val_eq, List.getElem?_set_ne (Ne.symm newest)]
      exact read

private theorem offset_value (offset : Usize) : (UScalar.cast .U64 offset).val = offset.val := by
  have bound : offset.val < 2 ^ System.Platform.numBits := offset.hBounds
  have platform : 2 ^ System.Platform.numBits ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) System.Platform.numBits_le
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (bound.trans_le platform)

open RootDivide in
/-- The original factor commit creates exactly one admitted stack slot
    and preserves the earlier coefficient regions. -/
def ActualCommitWithPendingLayout : Prop :=
  ∀ (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
    (meter : WorkMeter) (length start : Usize) (quotient remainder : Slice U64) (raw : Slice RawProduct)
    (polynomialWords : Nat),
    PendingLayout roots stack factors.length polynomialWords →
    roots.pending.val + 1 ≤ stack.length →
    (roots.pending.val + 1) * roots.stride.val ≤ factors.length →
    start.val = roots.pending.val * roots.stride.val →
    1 ≤ length.val → length.val ≤ roots.stride.val →
    (roots.affine = true → length.val < roots.stride.val) →
    let output := committed roots buffers factors stack meter length start quotient remainder raw
    let after := output.2.1
    let written := output.2.2.2.2.1
    let newStack := output.2.2.2.2.2.1
    PendingLayout after newStack written.length polynomialWords ∧
      ∀ index < start.val, written[index]! = factors[index]!

open RootDivide in
theorem commit_with_pending_layout : ActualCommitWithPendingLayout := by
  intro roots buffers factors stack meter length start quotient remainder raw polynomialWords
    layout stackRoom factorRoom startValue positive lengthRoom affineRoom
  have pendingMax : roots.pending.val + 1 ≤ Usize.max := stackRoom.trans stack.length_ineq
  let after := { roots with
    pending := usizeWord (roots.pending.val + 1)
    degree := roots.gcd_degree
    direction := directionWord roots
    checked := true
    affine_rank := if roots.affine then usizeWord (roots.affine_rank.val - 1) else roots.affine_rank }
  let frame : FactorFrame := ⟨UScalar.cast .U64 start, UScalar.cast .U64 length, directionWord roots, 1#u32⟩
  let copied := factors.setSlice! start.val (DenseCoefficient.prefixSlice quotient length.val).val
  have shape : SlotLayout roots roots.pending.val frame := by
    simp only [SlotLayout, frame, offset_value]
    exact ⟨startValue, positive, lengthRoom, affineRoom⟩
  have frameLayout :
      PendingLayout after (stack.set roots.pending frame) factors.length polynomialWords :=
    pushed_slots roots after stack factors.length polynomialWords frame layout stackRoom factorRoom
      shape (word_val _ pendingMax) rfl rfl
  have before (index : Nat) (earlier : index < start.val) : copied[index]! = factors[index]! :=
    Slice.setSlice!_getElem!_prefix _ _ _ _ earlier
  cases affine : roots.affine with
  | false =>
    simp only [committed, affine, Bool.false_eq_true, ite_false]
    refine ⟨?_, before⟩
    simpa only [after, affine, Bool.false_eq_true, ite_false, Slice.setSlice!_length, frame] using frameLayout
  | true =>
    let rank := usizeWord (roots.affine_rank.val - 1)
    let savedFrame := { frame with next_direction := UScalar.cast .U32 rank }
    let base := usizeWord (start.val + roots.stride.val - 1)
    let word := (buffers.basis.directions.map fun basis => basis[rank.val]!).getD 0#u64
    have affineLayout :
        PendingLayout after (stack.set roots.pending savedFrame) factors.length polynomialWords :=
      pushed_slots roots after stack factors.length polynomialWords savedFrame layout stackRoom factorRoom
        shape (word_val _ pendingMax) rfl rfl
    have collapsed : (stack.set roots.pending frame).set roots.pending savedFrame =
        stack.set roots.pending savedFrame := by
      apply Slice.ext
      simp only [Slice.set_val_eq, List.set_set]
    have endSlot : start.val + roots.stride.val ≤ factors.length := by
      rw [startValue, show roots.pending.val * roots.stride.val + roots.stride.val =
        (roots.pending.val + 1) * roots.stride.val by rw [Nat.add_mul, Nat.one_mul]]
      exact factorRoom
    have baseValue : base.val = start.val + roots.stride.val - 1 :=
      word_val _ ((Nat.sub_le ..).trans (endSlot.trans factors.length_ineq))
    simp only [committed, affine, ite_true]
    refine ⟨?_, ?_⟩
    · simp only [savedFrame, frame, rank] at collapsed
      simpa only [after, affine, ite_true, Slice.set_length, Slice.setSlice!_length, savedFrame, frame, rank, collapsed]
        using affineLayout
    · intro index earlier
      change (copied.set base (roots.affine_base ^^^ word))[index]! = _
      rw [Slice.getElem!_Nat_set_ne _ _ _ _ (by rw [baseValue]; omega)]
      exact before index earlier

end BulksketchBridge.RootRun
