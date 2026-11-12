import BulksketchBridge.PortableInsertion
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.PortableEncoding

open Aeneas Aeneas.Std BulksketchBridge.Algebra.Gf64
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
open bulksketch.backend.contract

private theorem encoding_loop_refines {Backend : Type}
    (kernels : BulkKernels Backend bulksketch.field.Gf64)
    (nativeInsert : ∀ odd ids, kernels.insert_nonzero odd ids =
      insert_nonzero bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField odd ids)
    (ids : Slice U64) (start : Nat) (bounded : start ≤ ids.length) (odd : Slice U64) :
    ∃ output : Slice U64,
      BulkKernels.encode_nonzero.default_loop kernels ⟨ids, start⟩ odd = Result.ok output ∧
      output.length = odd.length ∧
      ∀ slot, slot < odd.length → output[slot]! = foldColumn (ids.val.drop start) slot odd[slot]! := by
  suffices ∀ remaining start, start ≤ ids.length → ids.length - start = remaining →
    ∀ odd : Slice U64, ∃ output : Slice U64,
      BulkKernels.encode_nonzero.default_loop kernels ⟨ids, start⟩ odd = Result.ok output ∧
      output.length = odd.length ∧
      ∀ slot, slot < odd.length → output[slot]! = foldColumn (ids.val.drop start) slot odd[slot]!
    from this (ids.length - start) start bounded rfl odd
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro start bounded eq odd
    by_cases active : start < ids.length
    · let singleton : Slice U64 := Slice.from [ids[start]!] (by scalar_tac)
      have singletonNormal : bulksketch.core.slice.raw.from_ref ids[start]! = Result.ok singleton := rfl
      obtain ⟨next, inserted, nextLength, nextWords⟩ := insert_nonzero_refines odd singleton
      have step : BulkKernels.encode_nonzero.default_loop.body kernels ⟨ids, start⟩ odd =
          Result.ok (ControlFlow.cont (⟨ids, start + 1⟩, next)) := by
        simp only [BulkKernels.encode_nonzero.default_loop.body, shared_next ids start active, bind_ok]
        dsimp! only
        simp only [singletonNormal, bind_ok, nativeInsert, inserted]
      obtain ⟨output, normal, outputLength, words⟩ :=
        ih (ids.length - (start + 1)) (by omega) (start + 1) (by omega) rfl next
      refine ⟨output, ?_, outputLength.trans nextLength, ?_⟩
      · unfold BulkKernels.encode_nonzero.default_loop
        unfold loop
        dsimp only
        rw [step]
        simp only [bind_ok]
        exact normal
      · intro slot bound
        rw [words slot (by omega), nextWords slot bound, foldColumn_drop_step ids start slot odd[slot]! active]
        simp [foldColumn, singleton]
    · have terminal : start = ids.length := by omega
      subst start
      have done : BulkKernels.encode_nonzero.default_loop.body kernels ⟨ids, ids.length⟩ odd =
          Result.ok (ControlFlow.done odd) := by
        simp only [BulkKernels.encode_nonzero.default_loop.body, shared_done ids ids.length (Nat.le_refl _), bind_ok]
        dsimp! only
      refine ⟨odd, ?_, rfl, ?_⟩
      · unfold BulkKernels.encode_nonzero.default_loop
        unfold loop
        dsimp only
        simp only [done, bind_ok]
      · intro slot _
        simp [foldColumn]

/-- The original default clears its destination and produces exactly the same
word fold through the singleton and batch paths. -/
theorem encode_nonzero_refines : PortableEncodingChallenges.actualEncodeNonzeroReturnsFrame := by
  intro Backend kernels nativeInsert odd ids
  obtain ⟨zeros, fillNormal, zeroLength, zeroValues⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.Slice.fill.spec core.clone.CloneU64 odd 0#u64
      (by exact (WP.spec_ok (0#u64)).mpr rfl))
  have zeroWord : ∀ slot, slot < odd.length → zeros[slot]! = 0#u64 := by
    intro slot bounded
    rw [Slice.getElem!_Nat_eq, zeroValues]
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, bounded,
      ite_true, Option.getD_some]
  by_cases small : ids.length ≤ 2
  · have smallGuard : ids.len ≤ 2#usize := by
      rw [UScalar.le_equiv, Slice.len_val]
      simpa using small
    obtain ⟨output, normal, outputLength, words⟩ :=
      encoding_loop_refines kernels nativeInsert ids 0 (Nat.zero_le _) zeros
    refine ⟨output, ?_, outputLength.trans zeroLength, ?_⟩
    · simp only [BulkKernels.encode_nonzero.default, fillNormal, bind_ok, smallGuard, ite_true,
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, normal]
    · intro slot bounded
      rw [words slot (by omega), List.drop_zero, zeroWord slot bounded]
  · have largeGuard : ¬ ids.len ≤ 2#usize := by
      rw [UScalar.le_equiv, Slice.len_val]
      simpa using small
    obtain ⟨output, normal, outputLength, words⟩ := insert_nonzero_refines zeros ids
    refine ⟨output, ?_, outputLength.trans zeroLength, ?_⟩
    · simp only [BulkKernels.encode_nonzero.default, fillNormal, bind_ok, largeGuard, ite_false,
        nativeInsert, normal]
    · intro slot bounded
      rw [words slot (by omega), zeroWord slot bounded]

theorem oddPower_field (id : U64) (slot : Nat) :
    toField (oddPower id slot).bv = (toField id.bv) ^ (2 * slot + 1) := by
  induction slot with
  | zero => simp [oddPower, powerFrom]
  | succ slot ih =>
    change toField (multiplyWord (oddPower id slot).bv (Square.expectedWord id).bv) = _
    have squareMeaning : toField (Square.expectedWord id).bv = (toField id.bv) ^ 2 := toField_square id.bv
    rw [toField_mul, ih, squareMeaning, ← pow_add]
    congr 1

theorem foldColumn_field (ids : List U64) (slot : Nat) (initial : U64) :
    toField (foldColumn ids slot initial).bv =
      toField initial.bv + (ids.map fun id => (toField id.bv) ^ (2 * slot + 1)).sum := by
  induction ids generalizing initial with
  | nil => simp [foldColumn]
  | cons id ids ih =>
    change toField (foldColumn ids slot (initial ^^^ oddPower id slot)).bv = _
    rw [ih]
    change toField (initial.bv ^^^ (oddPower id slot).bv) + _ = _
    rw [toField_xor, oddPower_field]
    simp [add_assoc]

end BulksketchBridge.PortableEncoding
