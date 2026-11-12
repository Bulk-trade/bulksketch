import BulksketchBridge.PortableEncoding
import BulksketchBridge.RebuiltLocatorPolynomial

namespace BulksketchBridge.PortableEncoding

open Aeneas.Std Algebra.Gf64 RebuiltLfsr
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels

/-- Inserting distinct roots into the zeroed seed frame yields the odd
syndromes over their finite support. -/
theorem rebuilt_seed (shape roots : Slice U64) (distinct : roots.val.Nodup) :
    ∃ seed : Slice U64,
      insert_nonzero bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
        (zeroWords shape) roots = Result.ok seed ∧
      seed.length = shape.length ∧
      ∀ slot, slot < seed.length →
        toField seed[slot]!.bv = Reconciliation.oddSyndrome (rootSupport roots) slot := by
  classical
  obtain ⟨seed, normal, lengthEq, frame⟩ := insert_nonzero_refines (zeroWords shape) roots
  have zeroLength : (zeroWords shape).length = shape.length := by simp [zeroWords]
  refine ⟨seed, normal, lengthEq.trans zeroLength, ?_⟩
  intro slot bounded
  have inside : slot < shape.length := by rw [lengthEq, zeroLength] at bounded; exact bounded
  have zero : (zeroWords shape)[slot]! = 0#u64 := by simp [zeroWords, inside]
  rw [frame slot (by rw [← lengthEq]; exact bounded), zero, foldColumn_field]
  simp only [show (0#u64).bv = 0 from rfl, toField_zero, zero_add]
  have injective : Function.Injective (fun word : U64 => toField word.bv) := by
    intro left right equal
    apply U64.bv_eq_imp_eq
    exact toField_injective equal
  simp only [Reconciliation.oddSyndrome, Reconciliation.powerSum, rootSupport]
  rw [List.sum_toFinset _ (distinct.map injective), List.map_map]
  rfl

end BulksketchBridge.PortableEncoding
