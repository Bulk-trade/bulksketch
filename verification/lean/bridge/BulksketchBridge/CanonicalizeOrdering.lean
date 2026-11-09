import BulksketchBridge.DegreeProbeRuntime

namespace BulksketchBridge.CanonicalizeOrdering

open Aeneas.Std Aeneas.Std.DegreeProbeRuntime

/-- The value-level two-element branch of the canonicalizer. -/
def orderedPair (left right : U64) : List U64 :=
  if right.val < left.val then [right, left] else [left, right]

theorem orderedPair_perm (left right : U64) :
    (orderedPair left right).Perm [left, right] := by
  unfold orderedPair
  split
  · exact .swap _ _ _
  · rfl

theorem orderedPair_ordered (left right : U64) :
    (orderedPair left right).Pairwise ordered := by
  unfold orderedPair
  split <;> rename_i order
  · simpa [ordered] using Nat.le_of_lt order
  · simpa [ordered] using Nat.le_of_not_gt order

def adjacentDuplicate : List U64 → Bool
  | left :: (right :: rest) => decide (left = right) || adjacentDuplicate (right :: rest)
  | _ => false

/-- The read-only width-two Windows cursor emits a prefix and advances one word. -/
def pairWindows : List U64 → List (U64 × U64)
  | left :: (right :: rest) => (left, right) :: pairWindows (right :: rest)
  | _ => []

theorem pair_windows_length (words : List U64) :
    (pairWindows words).length = words.length - 1 := by
  induction words with
  | nil => rfl
  | cons left tail ih =>
    cases tail with
    | nil => rfl
    | cons right tail =>
      simp only [pairWindows, List.length_cons] at ih ⊢
      omega

theorem pair_windows_get (words : List U64) (index : Nat)
    (within : index + 1 < words.length) :
    (pairWindows words)[index]! = (words[index]!, words[index + 1]!) := by
  induction words generalizing index with
  | nil => simp at within
  | cons left tail ih =>
    cases tail with
    | nil => simp at within
    | cons right tail =>
      cases index with
      | zero => rfl
      | succ index =>
        have next : index + 1 < (right :: tail).length := by simp only [List.length_cons] at within ⊢; omega
        simpa only [pairWindows, List.getElem!_cons_succ] using ih index next

theorem windows_any_duplicate (words : List U64) :
    (pairWindows words).any (fun pair => decide (pair.1 = pair.2)) = adjacentDuplicate words := by
  induction words with
  | nil => rfl
  | cons left tail ih =>
    cases tail with
    | nil => rfl
    | cons right tail =>
      simp only [pairWindows, List.any_cons, adjacentDuplicate]
      rw [ih]

/-- An ascending row has duplicate words exactly when adjacent words coincide. -/
theorem adjacentDuplicate_false_iff_nodup (words : List U64)
    (ascending : words.Pairwise ordered) :
    adjacentDuplicate words = false ↔ words.Nodup := by
  induction words with
  | nil => simp [adjacentDuplicate]
  | cons left tail ih =>
    cases tail with
    | nil => simp [adjacentDuplicate]
    | cons right tail =>
      have tailAscending := (List.pairwise_cons.mp ascending).2
      rw [adjacentDuplicate]
      by_cases same : left = right
      · subst right
        simp
      · have forward : left.val ≤ right.val :=
          (List.pairwise_cons.mp ascending).1 right (by simp)
        have strict : left.val < right.val := by
          refine Nat.lt_of_le_of_ne forward ?_
          intro eq
          exact same (UScalar.eq_of_val_eq eq)
        have notMember : left ∉ right :: tail := by
          intro member
          rcases List.mem_cons.mp member with equal | inTail
          · exact same equal
          · have later : right.val ≤ left.val := (List.pairwise_cons.mp tailAscending).1 left inTail
            omega
        simp only [same, decide_false, Bool.false_or, List.nodup_cons, notMember,
          not_false_eq_true, true_and, ih tailAscending]


def orderWords (words : Slice U64) : Slice U64 :=
  match h : words.val with
  | [] | [_] => words
  | [left, right] =>
    Slice.from (orderedPair left right) (by
      rw [(orderedPair_perm left right).length_eq, ← h]
      exact words.length_ineq)
  | _ => sortedWords words

theorem order_words_eq_sorted (words : Slice U64) :
    orderWords words = sortedWords words := by
  apply DegreeProbeRuntime.canonical_unique
  · unfold orderWords
    split <;> rename_i eq
    · simp [eq]
    · simp [eq]
    · simp only [Slice.from_val]
      exact orderedPair_ordered _ _
    · exact DegreeProbeRuntime.sortedWords_ordered _
  · unfold orderWords
    split <;> rename_i eq
    · exact List.Perm.refl _
    · exact List.Perm.refl _
    · simp only [Slice.from_val, eq]
      exact orderedPair_perm _ _
    · exact DegreeProbeRuntime.sortedWords_perm _

def validWord (mask word : U64) : Prop :=
  word.bv ≠ 0 ∧ word.bv &&& (~~~mask.bv) = 0

def wordInvalid (mask word : U64) : Bool :=
  decide (word.bv = 0 ∨ word.bv &&& (~~~mask.bv) ≠ 0)

def invalid (mask : U64) (words : List U64) : Bool :=
  words.any (wordInvalid mask) || adjacentDuplicate words

theorem ordered_validation (mask : U64) (words : List U64)
    (ordered : words.Pairwise ordered) :
    invalid mask words = false ↔ (∀ word ∈ words, validWord mask word) ∧ words.Nodup := by
  simp only [invalid, Bool.or_eq_false_iff, List.any_eq_false, wordInvalid,
    decide_eq_true_eq, not_or, not_ne_iff, adjacentDuplicate_false_iff_nodup words ordered,
    validWord]

theorem complete_word_validation (mask : U64) (words : Slice U64) :
    invalid mask (orderWords words).val = false ↔
      (∀ word ∈ words.val, validWord mask word) ∧ words.val.Nodup := by
  rw [order_words_eq_sorted, ordered_validation _ _ (DegreeProbeRuntime.sortedWords_ordered words)]
  constructor <;> rintro ⟨admitted, distinct⟩
  · exact ⟨fun word member => admitted word ((DegreeProbeRuntime.sortedWords_perm words).mem_iff.mpr member),
      (DegreeProbeRuntime.sortedWords_perm words).nodup_iff.mp distinct⟩
  · exact ⟨fun word member => admitted word ((DegreeProbeRuntime.sortedWords_perm words).mem_iff.mp member),
      (DegreeProbeRuntime.sortedWords_perm words).nodup_iff.mpr distinct⟩


end BulksketchBridge.CanonicalizeOrdering
