import BulksketchBridge.PublicationWrite

namespace BulksketchBridge.PublicationWrite

open Aeneas.Std
open BulksketchBridge.CanonicalizeOrdering

private theorem strict_of_ordered (words : List U64)
    (ascending : words.Pairwise Aeneas.Std.DegreeProbeRuntime.ordered) (distinct : words.Nodup) :
    words.Pairwise (fun a b => a < b) := by
  induction words with
  | nil => exact .nil
  | cons first rest ih =>
    obtain ⟨ordered, tail⟩ := List.pairwise_cons.mp ascending
    obtain ⟨unique, restDistinct⟩ := List.nodup_cons.mp distinct
    refine List.pairwise_cons.mpr ⟨?_, ih tail restDistinct⟩
    intro later member
    have le : first.val ≤ later.val := ordered later member
    have different : first.val ≠ later.val := by
      intro equal
      exact unique ((UScalar.eq_of_val_eq equal).symm ▸ member)
    change first.val < later.val
    omega

private theorem strict_windows (words : List U64) (strict : words.Pairwise (fun a b => a < b)) :
    (pairWindows words).all (fun pair => decide (pair.1 < pair.2)) = true := by
  induction words with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨ordered, tail⟩ := List.pairwise_cons.mp strict
    cases rest with
    | nil => rfl
    | cons second rest =>
      have firstPair := ordered second (by simp)
      change (decide (first < second) &&
        (pairWindows (second :: rest)).all (fun pair => decide (pair.1 < pair.2))) = true
      rw [decide_eq_true_eq.mpr firstPair, ih tail]
      rfl

/-- The completed sorted root result supplies the original writer's exact
validation premises, including the empty-row zero-prefix rule. -/
theorem valid_decoded_of_canonical (ids : Slice U64) (zero : Bool)
    (nonempty : ids.val ≠ [] ∨ zero = true)
    (ascending : ids.val.Pairwise Aeneas.Std.DegreeProbeRuntime.ordered)
    (distinct : ids.val.Nodup) (nonzero : ∀ id ∈ ids.val, id ≠ 0#u64) :
    validDecoded ids zero := by
  refine ⟨nonempty, ?_, strict_windows _ (strict_of_ordered _ ascending distinct)⟩
  intro invalid
  cases words : ids.val with
  | nil => simp [words] at invalid
  | cons first rest =>
    have zeroFirst : first = 0#u64 := by simpa [words] using invalid
    exact nonzero first (by simp [words]) zeroFirst

#print axioms valid_decoded_of_canonical

end BulksketchBridge.PublicationWrite
