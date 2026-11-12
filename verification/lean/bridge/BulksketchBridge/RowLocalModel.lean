import BulksketchBridge.CandidateCompactWords
import BulksketchBridge.DegreeProbeRuntime

namespace BulksketchBridge.CandidateNormalization

open Aeneas.Std Aeneas.Std.DegreeProbeRuntime

/-- Row-local normalization sorts unsigned words and removes zero and
repeated occurrences within this row. Other rows have separate prefixes. -/
def normalizedRowWords (words : Slice U64) : List U64 :=
  compactedWords (sortedWords words).val

theorem normalized_row_distinct (words : Slice U64) : (normalizedRowWords words).Nodup :=
  compacted_words_distinct UScalar.val (fun _ _ equal => UScalar.eq_of_val_eq equal) _
    (BulksketchBridge.DegreeProbeRuntime.sortedWords_ordered words)

theorem normalized_row_mem (words : Slice U64) (word : U64) :
    word ∈ normalizedRowWords words ↔ word ∈ words.val ∧ word ≠ 0#u64 := by
  rw [normalizedRowWords, compacted_words_mem, (BulksketchBridge.DegreeProbeRuntime.sortedWords_perm words).mem_iff]

def localPayload (rows : List (Slice U64)) : List U64 :=
  rows.flatMap normalizedRowWords

def localOffset (rows : List (Slice U64)) (bucket : Nat) : Nat :=
  (localPayload (rows.take bucket)).length

/-- The consecutive offsets of the row-local model select exactly the
normalization of the corresponding input row. -/
theorem row_local_payload_slice (rows : List (Slice U64)) (bucket : Nat) (live : bucket < rows.length) :
    (localPayload rows).slice (localOffset rows bucket) (localOffset rows (bucket + 1)) =
      normalizedRowWords rows[bucket] := by
  let before := localPayload (rows.take bucket)
  let here := normalizedRowWords rows[bucket]
  let after := localPayload (rows.drop (bucket + 1))
  have original : rows = rows.take bucket ++ rows[bucket] :: rows.drop (bucket + 1) := by
    conv_rhs => rw [← List.drop_eq_getElem_cons live, List.take_append_drop]
  have layout : localPayload rows = before ++ here ++ after := by
    conv_lhs => rw [localPayload, original]
    simp only [List.flatMap_append, List.flatMap_cons, before, here, after, localPayload, List.append_assoc]
  have endAt : localOffset rows (bucket + 1) = before.length + here.length := by
    simp only [localOffset, localPayload, List.take_succ_eq_append_getElem live, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, before, here]
  unfold List.slice
  rw [layout, show localOffset rows bucket = before.length from rfl, endAt, Nat.add_sub_cancel_left]
  rw [List.append_assoc, List.drop_left]
  exact List.take_left

theorem row_local_packed_distinct (rows : List (Slice U64)) (bucket : Nat) (live : bucket < rows.length) :
    let hints := (localPayload rows).slice (localOffset rows bucket) (localOffset rows (bucket + 1))
    hints.Nodup ∧ ∀ word, word ∈ hints ↔ word ∈ rows[bucket].val ∧ word ≠ 0#u64 := by
  dsimp only
  rw [row_local_payload_slice rows bucket live]
  exact ⟨normalized_row_distinct _, normalized_row_mem _⟩

#print axioms row_local_packed_distinct

end BulksketchBridge.CandidateNormalization
