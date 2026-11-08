import BulksketchBridge.ReconstructionSpec
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.Reconstruction

open Aeneas Aeneas.Std Aeneas.Std.WP
open bulksketch.backend.contract bulksketch.decode.stages.Execution

private theorem read_normal (words : Slice U64) (index : Usize)
    (bounded : index.val < words.length) : Slice.index_usize words index = .ok words.val[index.val]! := by
  obtain ⟨word, normal, value⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words index bounded)
  rw [normal, value]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! words.val index.val bounded)

theorem update_normal (words : Slice U64) (index : Usize) (word : U64)
    (bounded : index.val < words.length) :
    Slice.update words index word = .ok (words.setAtNat index.val word) := by
  obtain ⟨output, normal, exactOutput⟩ := RawMulTable.normal_of_spec _ _ (Slice.update_spec words index word bounded)
  rw [normal, exactOutput]
  rfl

theorem initial_prefix (difference initial : Slice U64) (nonempty : 0 < initial.length) :
    Prefix difference initial (initial.setAtNat 0 0#u64) 1 := by
  refine ⟨Slice.setAtNat_length _ _ _, Slice.getElem!_Nat_setAtNat_eq _ _ _ nonempty, ?_, ?_⟩
  · intro index positive before
    omega
  · intro index after _
    exact Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega)

private theorem extend_prefix (difference initial current : Slice U64) (index : Nat)
    (positive : 0 < index) (bounded : index < initial.length)
    (inv : Prefix difference initial current index) :
    Prefix difference initial (current.setAtNat index (SyndromeStep difference current index)) (index + 1) := by
  have inCurrent : index < current.length := by rw [inv.length]; exact bounded
  refine ⟨(Slice.setAtNat_length _ _ _).trans inv.length, ?_, ?_, ?_⟩
  · rw [Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega), inv.sentinel]
  · intro p pPositive before
    have half : p / 2 ≠ index := by omega
    have stable : SyndromeStep difference (current.setAtNat index (SyndromeStep difference current index)) p =
        SyndromeStep difference current p := by
      unfold SyndromeStep
      rw [Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (Ne.symm half)]
    rw [stable]
    by_cases here : p = index
    · subst p
      exact Slice.getElem!_Nat_setAtNat_eq _ _ _ inCurrent
    · rw [Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (Ne.symm here)]
      exact inv.recurrence p pPositive (by omega)
  · intro p after inInitial
    rw [Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega)]
    exact inv.frame p (by omega) inInitial

private theorem next_active (range : Inclusive)
    (notStopped : ¬(range.exhausted = true ∨ range.«end».val < range.start.val)) :
    ∃ next : Inclusive,
      core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
        core.iter.range.StepUsize range = .ok (some range.start, next) ∧
      next.«end» = range.«end» ∧ range.start.val ≤ next.start.val ∧
      next.start.val ≤ range.«end».val + 1 ∧ processed next = range.start.val + 1 := by
  obtain ⟨⟨option, next⟩, normal, post⟩ := RawMulTable.normal_of_spec _ _
    (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec range)
  simp only [uncurry'_pair, ite_eq_right notStopped] at post
  by_cases advances : range.start.val < range.«end».val
  · rw [ite_eq_left advances] at post
    obtain ⟨rfl, startEq, endEq, exhaustedEq⟩ := post
    refine ⟨next, normal, endEq, by omega, by omega, ?_⟩
    simp [processed, exhaustedEq, startEq]
  · rw [ite_eq_right advances] at post
    obtain ⟨rfl, startEq, endEq, exhaustedEq⟩ := post
    refine ⟨next, normal, endEq, by simp [startEq], by simp [startEq]; omega, ?_⟩
    simp [processed, exhaustedEq, endEq]
    omega

private theorem body_active {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (square : ∀ word, kernels.ArithmeticInst.square word = .ok (squareWord word))
    (range next : Inclusive) (difference current : Slice U64)
    (step : core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
        core.iter.range.StepUsize range = .ok (some range.start, next))
    (positive : 0 < range.start.val) (bounded : range.start.val ≤ 2 * difference.length)
    (inCurrent : range.start.val < current.length) :
    reconstruct_loop0.body field kernels difference range current =
      .ok (.cont (next, current.setAtNat range.start.val (SyndromeStep difference current range.start.val))) := by
  obtain ⟨half, divides, halfValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.div_spec range.start (y := 2#usize) (by simp))
  have halfEq : half.val = range.start.val / 2 := by simpa using halfValue
  have parity : core.num.Usize.is_multiple_of range.start 2#usize =
      .ok (decide (range.start.val % 2 = 0)) := by
    change Result.ok (range.start.val % 2 == 0) = _
    congr 1
  simp only [reconstruct_loop0.body, step, bind_ok]
  dsimp! only
  by_cases even : range.start.val % 2 = 0
  · have halfBound : half.val < current.length := by omega
    simp only [parity, even, decide_true, ite_true, divides,
      read_normal current half halfBound, square, halfEq, SyndromeStep, bind_ok]
    simp only [update_normal _ _ _ inCurrent, bind_ok]
  · have halfBound : half.val < difference.length := by omega
    simp only [parity, even, decide_false, Bool.false_eq_true,
      ite_false, divides, read_normal difference half halfBound, halfEq, SyndromeStep, bind_ok]
    simp only [update_normal _ _ _ inCurrent, bind_ok]

theorem reconstruct_loop0_refines : ActualReconstructionLoop0 := by
  intro F K field kernels range difference initial current square starts endPlus endExact room inv
  suffices run : ∀ remaining (range : Inclusive) (current : Slice U64),
      2 * difference.length + 1 - processed range = remaining →
      1 ≤ range.start.val → range.start.val ≤ range.«end».val + 1 →
      range.«end».val = 2 * difference.length →
      Prefix difference initial current (processed range) →
      ∃ final, reconstruct_loop0 field kernels range difference current = .ok final ∧
        Prefix difference initial final (2 * difference.length + 1) from
    run _ range current rfl starts endPlus endExact inv
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro range current count starts endPlus endExact inv
    by_cases stop : range.exhausted = true ∨ range.«end».val < range.start.val
    · obtain ⟨⟨option, next⟩, normal, post⟩ := RawMulTable.normal_of_spec _ _
        (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec range)
      simp only [uncurry'_pair, ite_eq_left stop] at post
      obtain ⟨optionEq, nextEq⟩ := post
      rw [optionEq, nextEq] at normal
      have finished : processed range = 2 * difference.length + 1 := by
        cases exhausted : range.exhausted with
        | true => simp [processed, exhausted, endExact]
        | false =>
          have beyond : range.«end».val < range.start.val := stop.resolve_left (by simp [exhausted])
          have atEnd : range.start.val = range.«end».val + 1 :=
            Nat.le_antisymm endPlus (by omega)
          simp [processed, exhausted, atEnd, endExact]
      refine ⟨current, ?_, finished ▸ inv⟩
      unfold reconstruct_loop0 loop
      dsimp only
      simp only [reconstruct_loop0.body, normal, bind_ok]
      dsimp! only
      simp only [bind_ok]
    · have active : range.start.val ≤ range.«end».val := by omega
      have openRange : range.exhausted = false := by cases h : range.exhausted <;> simp_all
      have processedStart : processed range = range.start.val := by simp [processed, openRange]
      obtain ⟨next, step, endEq, startsMono, nextBound, advanced⟩ := next_active range stop
      have roomNow : range.start.val < current.length := by rw [inv.length]; omega
      have body := body_active field kernels square range next difference current step (by omega) (by omega) roomNow
      rw [processedStart] at inv
      have updated := extend_prefix difference initial current range.start.val (by omega) (by omega) inv
      rw [← advanced] at updated
      obtain ⟨final, result, exactFinal⟩ := ih (2 * difference.length + 1 - processed next)
        (by omega) next _ rfl (by omega) (by rw [endEq]; exact nextBound)
        (by rw [endEq]; exact endExact) updated
      refine ⟨final, ?_, exactFinal⟩
      conv => lhs; unfold reconstruct_loop0 loop
      dsimp only
      simp only [body, bind_ok]
      exact result

theorem reconstruct_loop1_refines : ActualReconstructionLoop1 := by
  exact reconstruct_loop0_refines

end BulksketchBridge.Reconstruction
