import BulksketchBridge.AffineSolveMapPivots

namespace BulksketchBridge.AffineSolveMap

open Aeneas.Std
open FrobeniusTables (entry entry_set_same entry_set_other)

def XorLinear (map : U64 → U64) : Prop :=
  map 0#u64 = 0#u64 ∧ ∀ x y, map (x ^^^ y) = map x ^^^ map y

def Graph (map : U64 → U64) (images preimages : Columns) : Prop :=
  ∀ i, i < 64 → entry images i ≠ 0#u64 → map (entry preimages i) = entry images i

/-- The same paired xor updates preserve the graph of a binary linear map. -/
theorem reduce_graph {images preimages : Columns} {original image reduced final : U64}
    (map : U64 → U64) (linear : XorLinear map) (graph : Graph map images preimages)
    (path : Reduced images preimages original image reduced final) (correct : map original = image) :
    map reduced = final := by
  induction path with
  | zero => exact correct
  | vacant => exact correct
  | cancel original image _ _ active occupied _ inductionHypothesis =>
    apply inductionHypothesis
    rw [linear.2, correct, graph _ (pivot_lt_width image active) occupied]

theorem insert_graph {images preimages : Columns} {image original : U64}
    (map : U64 → U64) (graph : Graph map images preimages) (imageOf : map original = image) :
    Graph map (inserted images image image) (inserted preimages image original) := by
  by_cases zero : image = 0#u64
  · simpa only [inserted, zero, ite_true] using graph
  · simp only [inserted, zero, ite_false]
    intro i inside present
    by_cases same : i = (pivotWord image).val
    · subst i
      rw [entry_set_same _ _ _ inside, entry_set_same _ _ _ inside, imageOf]
    · rw [entry_set_other _ _ _ _ (Ne.symm same), entry_set_other _ _ _ _ (Ne.symm same)]
      apply graph _ inside
      simpa only [entry_set_other _ _ _ _ (Ne.symm same)] using present

/-- On a successful target reduction the reported preimage maps to the
original target. The graph condition concerns only occupied source pivots. -/
theorem reduce_target_graph {images preimages : Columns} {solution target reduced final : U64}
    (map : U64 → U64) (linear : XorLinear map) (graph : Graph map images preimages)
    (path : Reduced images preimages solution target reduced final) :
    map reduced ^^^ final = map solution ^^^ target := by
  induction path with
  | zero => rfl
  | vacant => rfl
  | cancel solution target reduced final active occupied _ inductionHypothesis =>
    rw [inductionHypothesis, linear.2, graph _ (pivot_lt_width target active) occupied]
    apply U64.bv_eq_imp_eq
    let a := (map solution).bv
    let b := (entry images (pivot target)).bv
    let c := target.bv
    change (a ^^^ b) ^^^ (c ^^^ b) = a ^^^ c
    apply BitVec.eq_of_getLsbD_eq
    intro i bound
    simp only [BitVec.getLsbD_xor]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

#print axioms reduce_graph
#print axioms insert_graph
#print axioms reduce_target_graph

end BulksketchBridge.AffineSolveMap
