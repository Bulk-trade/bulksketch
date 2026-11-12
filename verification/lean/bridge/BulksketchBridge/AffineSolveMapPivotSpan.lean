import BulksketchBridge.AffineSolveMapPivots

namespace BulksketchBridge.AffineSolveMap

open Aeneas.Std FrobeniusTables

def xorRowSum : List U64 → U64
  | [] => 0#u64
  | row :: rest => row ^^^ xorRowSum rest

private theorem zero_bit_of_rows (rows : List U64) (bit : Nat)
    (clear : ∀ row ∈ rows, row.bv.getLsbD bit = false) :
    (xorRowSum rows).bv.getLsbD bit = false := by
  induction rows with
  | nil =>
    change (0 : BitVec 64).getLsbD bit = false
    simp
  | cons row rows ih =>
    change (row.bv ^^^ (xorRowSum rows).bv).getLsbD bit = false
    rw [BitVec.getLsbD_xor, clear row (List.mem_cons_self ..),
      ih (fun value member => clear value (List.mem_cons_of_mem _ member))]
    rfl

/-- Distinct ordered pivot rows cannot cancel the least pivot of their
    first row. This is the image independence used by the native sweep. -/
theorem xor_sum_least_pivot (first : U64) (rest : List U64) (present : first ≠ 0#u64)
    (ordered : ∀ row ∈ rest, pivot first < pivot row) :
    xorRowSum (first :: rest) ≠ 0#u64 ∧ pivot (xorRowSum (first :: rest)) = pivot first := by
  let sum := xorRowSum (first :: rest)
  have upperRows (bit : Nat) (atMost : bit ≤ pivot first) :
      (xorRowSum rest).bv.getLsbD bit = false := by
    apply zero_bit_of_rows
    intro row member
    exact BitVec.getLsbD_false_of_lt_ctz (atMost.trans_lt (ordered row member))
  have atFirst : sum.bv.getLsbD (pivot first) = true := by
    change (first.bv ^^^ (xorRowSum rest).bv).getLsbD (pivot first) = true
    rw [BitVec.getLsbD_xor, pivot_set first present, upperRows _ le_rfl]
    rfl
  have earlier (bit : Nat) (below : bit < pivot first) : sum.bv.getLsbD bit = false := by
    change (first.bv ^^^ (xorRowSum rest).bv).getLsbD bit = false
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_false_of_lt_ctz below, upperRows _ below.le]
    rfl
  have nonzero : sum ≠ 0#u64 := by
    intro zero
    rw [zero] at atFirst
    change (0 : BitVec 64).getLsbD (pivot first) = true at atFirst
    simp at atFirst
  refine ⟨nonzero, Nat.le_antisymm ?_ ?_⟩
  · by_contra! above
    have impossible := BitVec.getLsbD_false_of_lt_ctz (x := sum.bv) above
    rw [atFirst] at impossible
    contradiction
  · by_contra! below
    have impossible := earlier (pivot sum) below
    rw [pivot_set sum nonzero] at impossible
    contradiction

/-- A nonzero residue at a vacant pivot lies outside every sorted
    combination of occupied image rows. -/
theorem vacant_residue_excludes (images : Columns) (final : U64) (nonzero : final ≠ 0#u64)
    (vacant : entry images (pivot final) = 0#u64) (rows : List U64)
    (occupied : ∀ row ∈ rows, entry images (pivot row) = row ∧ row ≠ 0#u64)
    (ordered : rows.Pairwise (fun left right => pivot left < pivot right)) :
    xorRowSum rows ≠ final := by
  cases rows with
  | nil =>
    intro equal
    exact nonzero equal.symm
  | cons first rest =>
    intro equal
    obtain ⟨installed, present⟩ := occupied first (List.mem_cons_self ..)
    have least := (xor_sum_least_pivot first rest present (List.pairwise_cons.mp ordered).1).2
    rw [equal] at least
    rw [least, installed] at vacant
    exact present vacant

#print axioms xor_sum_least_pivot
#print axioms vacant_residue_excludes

end BulksketchBridge.AffineSolveMap
