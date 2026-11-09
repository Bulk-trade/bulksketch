import BulksketchBridge.RootPendingProduct
import BulksketchBridge.NativeDeflateResidual

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial DenseCoefficient RebuiltLfsr SliceKernels
open bulksketch.decode.roots bulksketch.decode.scratch

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

set_option maxRecDepth 4096

noncomputable def rootsProduct (words : List U64) : Polynomial Field :=
  (words.map fun word => X + C (toField word.bv)).prod

noncomputable def emittedProduct (roots : Roots) (workspace : RowWorkspace) : Polynomial Field :=
  rootsProduct (workspace.roots.val.take roots.count.val)

/-- The native deflation product uses the same factors as the exact
    emitted-word list, in the same admitted slice window. -/
theorem deflate_root_product_words (roots : Slice U64) (start count : Nat)
    (room : start + count ≤ roots.length) :
    Deflation.rootProduct roots start count = rootsProduct ((roots.val.drop start).take count) := by
  induction count generalizing start with
  | zero => simp only [Deflation.rootProduct, List.take_zero, rootsProduct, List.map_nil, List.prod_nil]
  | succ count ih =>
    have active : start < roots.val.length := by change start + (count + 1) ≤ roots.val.length at room; omega
    rw [Deflation.rootProduct, List.drop_eq_getElem_cons active, List.take_succ_cons]
    have rest : Deflation.rootProduct roots (start + 1) count =
        rootsProduct ((roots.val.drop (start + 1)).take count) := ih (start + 1) (by omega)
    rw [rest]
    simp only [rootsProduct, List.map_cons, List.prod_cons, Slice.getElem!_Nat_eq,
      List.Inhabited_getElem_eq_getElem! _ _ active]

private theorem word_injective : Function.Injective (fun word : U64 => toField word.bv) :=
  fun left right equal => U64.bv_eq_imp_eq left right (toField_injective equal)

/-- A proved emitted root list factors the monic split polynomial exactly. -/
theorem factor_from_emitted_roots (factor : Polynomial Field) (words : List U64)
    (monic : factor.Monic) (split : factor.Splits) (simple : factor.roots.Nodup)
    (distinct : words.Nodup)
    (complete : ∀ point, factor.IsRoot point ↔ ∃ word ∈ words, point = toField word.bv) :
    factor = rootsProduct words := by
  let represented := words.map (fun word : U64 => toField word.bv)
  have noDuplicates : (represented : Multiset Field).Nodup := by
    exact distinct.map word_injective
  have same : factor.roots = (represented : Multiset Field) := by
    apply (Multiset.Nodup.ext simple noDuplicates).mpr
    intro point
    rw [mem_roots monic.ne_zero]
    change factor.IsRoot point ↔ point ∈ represented
    rw [complete point, show represented = words.map _ from rfl, List.mem_map]
    exact ⟨fun ⟨word, member, equation⟩ => ⟨word, member, equation.symm⟩,
      fun ⟨word, member, equation⟩ => ⟨word, member, equation.symm⟩⟩
  rw [split.eq_prod_roots_of_monic monic, same]
  unfold rootsProduct
  simp only [represented, Multiset.map_coe, Multiset.prod_coe, List.map_map,
    sub_eq_add_neg, CharTwo.neg_eq]
  rfl

/-- The exact source emission appends the root words to the previously
committed prefix, so its represented polynomial gains exactly their factor. -/
theorem emitted_product_append (old written : Slice U64) (words : List U64) (count : Nat)
    (room : count + words.length ≤ old.length)
    (effect : written = old.setSlice! count words) :
    rootsProduct (written.val.take (count + words.length)) =
      rootsProduct (old.val.take count) * rootsProduct words := by
  have oldRoom : count ≤ old.val.length := by
    change count + words.length ≤ old.val.length at room
    omega
  have wordsRoom : words.length ≤ old.val.length - count := by
    change count + words.length ≤ old.val.length at room
    omega
  have width : (old.val.take count ++ words).length = count + words.length := by
    rw [List.length_append, List.length_take, Nat.min_eq_left oldRoom]
  have prefixWords : written.val.take (count + words.length) = old.val.take count ++ words := by
    rw [effect, Slice.setSlice!_val, List.setSlice!]
    simp only [Nat.min_eq_left wordsRoom, List.take_length]
    rw [← width, List.take_left]
  simp only [prefixWords, rootsProduct, List.map_append, List.prod_append]

/-- The product held by a traversal state. At verification, all
nonconstant factors have been emitted and the source may retain the last
active polynomial in scratch. -/
noncomputable def traversalProduct (finished : Bool) (roots : Roots) (workspace : RowWorkspace) :
    Polynomial Field :=
  if finished then emittedProduct roots workspace
  else emittedProduct roots workspace * liveProduct roots workspace

/-- Exact root append and exact pending restoration preserve the original
locator product across a leaf transition, including the terminal branch. -/
theorem emission_preserves_traversal_product (roots after : Roots) (old written : RowWorkspace)
    (words : List U64) (finished : Bool)
    (room : roots.count.val + words.length ≤ old.roots.length)
    (count : after.count.val = roots.count.val + words.length)
    (effect : written.roots = old.roots.setSlice! roots.count.val words)
    (factor : activeFactor roots old = rootsProduct words)
    (rest : pendingProduct old roots.pending.val = if finished then 1 else liveProduct after written) :
    traversalProduct finished after written = traversalProduct false roots old := by
  have appended : emittedProduct after written = emittedProduct roots old * rootsProduct words := by
    unfold emittedProduct
    rw [count]
    exact emitted_product_append old.roots written.roots words roots.count.val room effect
  cases finished
  · simp only [traversalProduct, Bool.false_eq_true, ite_false, appended, liveProduct, factor] at *
    rw [rest]
    exact mul_assoc ..
  · simp only [traversalProduct, Bool.false_eq_true, ite_false, ite_true, appended, liveProduct, factor] at *
    rw [rest, mul_one]

#print axioms factor_from_emitted_roots
#print axioms emitted_product_append

end BulksketchBridge.RootRun
