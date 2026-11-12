import BulksketchBridge.AvxRecurrenceOuter

namespace BulksketchBridge.AvxRecurrence

open Aeneas Aeneas.Std Result Aeneas.Std.AvxSquareRuntime
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- Every successful block covers its entire live slice, while the first
failed block terminates immediately with the original false result. -/
theorem outer_loop_refines (loadModel : Load) (loadLaw : AvxSquare.LoadLaw loadModel)
    (innerLaw : InnerBlockLaw loadModel) (odd squared : Slice U64) (index degree : Usize)
    (degreeBound : degree.val < squared.length) (atLeast : degree.val ≤ index.val) :
    ∃ answer : Bool,
      odd_recurrence_matches_loop0 loadModel (blockAt index odd.len) odd squared degree = .ok answer ∧
      (answer = true ↔ MatchesInterval odd squared degree.val index.val odd.length) := by
  suffices ∀ fuel (index : Usize), odd.length - index.val = fuel → degree.val ≤ index.val →
      ∃ answer : Bool,
        odd_recurrence_matches_loop0 loadModel (blockAt index odd.len) odd squared degree = .ok answer ∧
        (answer = true ↔ MatchesInterval odd squared degree.val index.val odd.length) by
    exact this _ index rfl atLeast
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro index remaining atLeast
    by_cases active : index.val < odd.length
    · obtain ⟨next, nextValue, advance, mismatch⟩ :=
        outer_block_active loadModel loadLaw innerLaw odd squared index degree degreeBound atLeast active
      have progress : index.val < next.val := by omega
      have bounded : next.val ≤ odd.length := by omega
      by_cases agrees : MatchesInterval odd squared degree.val index.val next.val
      · obtain ⟨answer, remainder, correct⟩ :=
          ih (odd.length - next.val) (by omega) next rfl (by omega)
        refine ⟨answer, ?_, ?_⟩
        · rw [odd_recurrence_matches_loop0, loop, advance agrees, bind_ok]
          exact remainder
        · constructor
          · intro yes position first last
            by_cases current : position < next.val
            · exact agrees position first current
            · exact correct.mp yes position (by omega) last
          · intro all
            exact correct.mpr (fun position first last => all position (by omega) last)
      · refine ⟨false, ?_, ?_⟩
        · rw [odd_recurrence_matches_loop0, loop, mismatch agrees, bind_ok]
        · simp only [Bool.false_eq_true, false_iff]
          intro all
          exact agrees (fun position first last => all position first (last.trans_le bounded))
    · have exhausted := outer_block_done loadModel odd squared index degree (by omega)
      refine ⟨true, ?_, ?_⟩
      · rw [odd_recurrence_matches_loop0, loop, exhausted, bind_ok]
      · constructor
        · intro _ position first last
          omega
        · intro _
          rfl

/-- The original AVX continuation agrees with the scalar GF64 recurrence
on every index at or above the squared locator degree. A longer locator
than the odd sequence gives an empty continuation. -/
def ActualAvxRecurrenceFromInner : Prop :=
  ∀ (loadModel : Load), AvxSquare.LoadLaw loadModel → InnerBlockLaw loadModel →
  ∀ (odd squared : Slice U64), 0 < squared.length →
    ∃ answer : Bool,
      odd_recurrence_matches loadModel odd squared = .ok answer ∧
      (answer = true ↔ OddRecurrence.continuationMatches odd squared)

theorem native_avx_recurrence_from_inner : ActualAvxRecurrenceFromInner := by
  intro loadModel loadLaw innerLaw odd squared positive
  obtain ⟨degree, subtracted, value, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := squared.len) (y := 1#usize) (by
      change 1 ≤ squared.len.val
      rw [Slice.len_val]
      omega))
  change degree.val = squared.len.val - 1 at value
  rw [Slice.len_val] at value
  have iterator : core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := degree, «end» := odd.len } 8#usize =
        .ok (blockAt degree odd.len) := rfl
  obtain ⟨answer, loopResult, correct⟩ :=
    outer_loop_refines loadModel loadLaw innerLaw odd squared degree degree (by omega) le_rfl
  refine ⟨answer, ?_, ?_⟩
  · rw [odd_recurrence_matches, subtracted, bind_ok]
    dsimp! only
    rw [iterator, bind_ok]
    exact loopResult
  · rw [correct]
    unfold MatchesInterval OddRecurrence.continuationMatches
    rw [value]

#print axioms outer_loop_refines
#print axioms native_avx_recurrence_from_inner

end BulksketchBridge.AvxRecurrence
