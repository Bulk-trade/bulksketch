import Arithmetic.Funs
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Tauto

namespace BulksketchBridge.CandidateNormalization

open Aeneas.Std

/-- The source inspects the most recently retained word. A reversed
accumulator models that access without an index. -/
def compactStep (reversed : List U64) (word : U64) : List U64 :=
  if word = 0#u64 ∨ reversed.head? = some word then reversed else word :: reversed

def compactedWords (words : List U64) : List U64 :=
  (words.foldl compactStep []).reverse

private theorem head_mem {word : U64} {words : List U64} (last : words.head? = some word) :
    word ∈ words := by
  cases words with
  | nil => simp at last
  | cons first rest => exact List.mem_cons.mpr (.inl (Option.some.inj last).symm)

private theorem step_mem (reversed : List U64) (word target : U64) :
    target ∈ compactStep reversed word ↔ target ∈ reversed ∨ target = word ∧ word ≠ 0#u64 := by
  by_cases zero : word = 0#u64
  · simp only [compactStep, zero, true_or, ite_true, ne_eq, not_true_eq_false,
      and_false, or_false]
  · by_cases repeated : reversed.head? = some word
    · have belongs := head_mem repeated
      simp only [compactStep, zero, repeated, or_true, ite_true, ne_eq, not_false_eq_true, and_true]
      constructor
      · exact Or.inl
      · rintro (member | rfl)
        · exact member
        · exact belongs
    · simp only [compactStep, zero, repeated, or_self, ite_false, List.mem_cons,
        ne_eq, not_false_eq_true, and_true, or_comm]

private theorem fold_mem (words reversed : List U64) (target : U64) :
    target ∈ words.foldl compactStep reversed ↔
      target ∈ reversed ∨ target ∈ words ∧ target ≠ 0#u64 := by
  induction words generalizing reversed with
  | nil => simp
  | cons word rest ih =>
    rw [List.foldl_cons, ih, step_mem]
    simp only [List.mem_cons]
    constructor
    · rintro ((old | ⟨same, nonzero⟩) | ⟨later, nonzero⟩)
      · exact Or.inl old
      · exact Or.inr ⟨Or.inl same, same ▸ nonzero⟩
      · exact Or.inr ⟨Or.inr later, nonzero⟩
    · rintro (old | ⟨same | later, nonzero⟩)
      · exact Or.inl (Or.inl old)
      · exact Or.inl (Or.inr ⟨same, same ▸ nonzero⟩)
      · exact Or.inr ⟨later, nonzero⟩

/-- The last-word guard drops neither a distinct input nor a repeated
value's only retained occurrence. -/
theorem compacted_words_mem (words : List U64) (target : U64) :
    target ∈ compactedWords words ↔ target ∈ words ∧ target ≠ 0#u64 := by
  simp only [compactedWords, List.mem_reverse, fold_mem, List.not_mem_nil, false_or]

private theorem fold_strict (key : U64 → Nat) (injective : Function.Injective key)
    (words reversed : List U64)
    (sorted : words.Pairwise (fun a b => key a ≤ key b))
    (strict : reversed.Pairwise (fun a b => key b < key a))
    (ordered : ∀ old ∈ reversed, ∀ new ∈ words, key old ≤ key new) :
    (words.foldl compactStep reversed).Pairwise (fun a b => key b < key a) := by
  induction words generalizing reversed with
  | nil => exact strict
  | cons word rest ih =>
    obtain ⟨headBound, tailSorted⟩ := List.pairwise_cons.mp sorted
    rw [List.foldl_cons]
    by_cases skip : word = 0#u64 ∨ reversed.head? = some word
    · rw [compactStep, ite_eq_left skip]
      exact ih reversed tailSorted strict
        (fun old seen new later => ordered old seen new (List.mem_cons_of_mem _ later))
    · rw [compactStep, ite_eq_right skip]
      apply ih (word :: reversed) tailSorted
      · apply List.pairwise_cons.mpr
        refine ⟨?_, strict⟩
        intro old seen
        cases reversed with
        | nil => simp at seen
        | cons latest earlier =>
          have latestLe := ordered latest (by simp) word (by simp)
          have notEqual : latest ≠ word := by
            intro equal
            exact skip (.inr (by simp [equal]))
          have latestLt : key latest < key word := Nat.lt_of_le_of_ne latestLe
            (fun equal => notEqual (injective equal))
          rcases List.mem_cons.mp seen with same | before
          · simpa only [same] using latestLt
          · exact ((List.pairwise_cons.mp strict).1 old before).trans latestLt
      · intro old seen new later
        rcases List.mem_cons.mp seen with same | earlier
        · simpa only [same] using headBound new later
        · exact ordered old earlier new (List.mem_cons_of_mem _ later)

/-- The source's last-word guard suffices for global distinctness on a
nondecreasing input under an injective sort key. -/
theorem compacted_words_distinct (key : U64 → Nat) (injective : Function.Injective key)
    (words : List U64) (sorted : words.Pairwise (fun a b => key a ≤ key b)) :
    (compactedWords words).Nodup := by
  have strict := fold_strict key injective words [] sorted .nil (by simp)
  have distinct : (words.foldl compactStep []).Nodup := by
    apply strict.imp
    intro left right lower equal
    rw [equal] at lower
    exact (Nat.lt_irrefl _ lower)
  simpa only [compactedWords, List.nodup_reverse] using distinct

def bucketKey (bucketCount : Nat) (word : U64) : Nat :=
  (word.val % bucketCount) * 2 ^ 64 + word.val

theorem bucket_key_injective (bucketCount : Nat) : Function.Injective (bucketKey bucketCount) := by
  intro left right same
  have residue (word : U64) : bucketKey bucketCount word % (2 ^ 64) = word.val := by
    unfold bucketKey
    rw [Nat.mul_comm (word.val % bucketCount), Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (show word.val < 2 ^ 64 from word.hBounds)
  exact UScalar.eq_of_val_eq ((residue left).symm.trans ((congrArg (fun n : Nat => n % (2 ^ 64)) same).trans
    (residue right)))

#print axioms compacted_words_distinct

end BulksketchBridge.CandidateNormalization
