import BulksketchBridge.CompletedLocator
import BulksketchBridge.RootFactorValidity

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

theorem roots_product_roots (words : List U64) :
    (rootsProduct words).roots = ((words.map fun word => toField word.bv) : Multiset Field) := by
  have exactRoots := roots_multiset_prod_X_sub_C ((words.map fun word => toField word.bv) : Multiset Field)
  simpa only [Multiset.map_coe, Multiset.prod_coe, List.map_map, Function.comp_def,
    sub_eq_add_neg, CharTwo.neg_eq, rootsProduct] using exactRoots

theorem emitted_words_valid (words : List U64) (locator : Polynomial Field)
    (represented : rootsProduct words = locator) (simple : locator.roots.Nodup)
    (nonzero : ∀ point, locator.IsRoot point → point ≠ 0) :
    (∀ word ∈ words, word.bv ≠ 0) ∧ words.Nodup := by
  constructor
  · intro word member zero
    apply nonzero 0
    · rw [← represented, CompletedResult.roots_product_root]
      exact ⟨word, member, by rw [zero, toField_zero]⟩
    · rfl
  · rw [← represented, roots_product_roots, Multiset.coe_nodup] at simple
    exact @List.Nodup.of_map U64 Field (fun word => toField word.bv) words simple

#print axioms emitted_words_valid

end BulksketchBridge.RootRun
