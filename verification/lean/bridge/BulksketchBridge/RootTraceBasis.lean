import BulksketchBridge.RootTraceSpec

namespace BulksketchBridge.RootTrace

open Aeneas Aeneas.Std Aeneas.Std.WP FrobeniusTables
open bulksketch.decode.roots bulksketch.backend.contract
open bulksketch.field.Gf64.Insts

set_option maxRecDepth 2048

theorem seed_nonzero (seed : U64) : basisSeed seed ≠ 0#u64 := by
  unfold basisSeed
  split
  · rename_i positive
    intro zero
    subst seed
    contradiction
  · decide

theorem seed_closure_refines : ActualSeedClosure := by
  intro K backend seed length
  let fresh := (Array.repeat 64#usize 0#u64).set 0#usize (basisSeed seed)
  refine ⟨?_, ?_⟩
  · have mask : seed &&& BulksketchFieldBinaryField.MASK = seed := by
      apply U64.bv_eq_imp_eq
      rw [BulksketchFieldBinaryField.MASK]
      change seed.bv &&& (-1 : BitVec 64) = seed.bv
      exact BitVec.and_allOnes
    have put := update_normal (Array.repeat 64#usize (0#u64 : U64)) 0#usize (basisSeed seed) (by decide)
    have seedEq : core.cmp.impls.OrdU64.max seed 1#u64 = basisSeed seed := rfl
    simp only [Roots.trace.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU6464.call_once,
      bind_ok, lift]
    change Aeneas.Std.bind ((Array.repeat 64#usize 0#u64).update 0#usize
      (core.cmp.impls.OrdU64.max (seed &&& BulksketchFieldBinaryField.MASK) 1#u64))
      (fun value => .ok (value, (seed, 1#u32))) = _
    rw [mask, seedEq, put, bind_ok]
    rfl
  · intro i below
    have iz : i = 0 := by omega
    subst i
    exact entry_set_same _ 0#usize _ (by decide)

private theorem next_arithmetic (word : U64) :
    ((⟨(word.bv : BitVec 64) <<< (1 : Nat)⟩ : U64) &&& BulksketchFieldBinaryField.MASK) ^^^
      (BulksketchFieldBinaryField.MODULUS_LOW &&&
        core.num.U64.wrapping_sub 0#u64 ⟨(word.bv : BitVec 64) >>> (63 : Nat)⟩) = basisNext word := by
  apply U64.bv_eq_imp_eq
  rw [BulksketchFieldBinaryField.MASK, BulksketchFieldBinaryField.MODULUS_LOW]
  change ((word.bv <<< (1 : Nat)) &&& (-1 : BitVec 64)) ^^^
    (27 &&& (0 - (word.bv >>> (63 : Nat)))) = _
  rw [show (-1 : BitVec 64) = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
  rfl

private theorem extend_step (seed : U64) (direction length : U32) (basis : Basis)
    (directionBound : direction.val < 64) (active : length.val ≤ direction.val)
    (positive : 1 ≤ length.val) (correct : cachePrefix seed basis length.val) :
    ∃ next updated,
      Roots.trace_loop0.body gf64 direction length basis = .ok (.cont (next, updated)) ∧
      next.val = length.val + 1 ∧ cachePrefix seed updated next.val ∧
      (∀ i, i ≠ length.val → entry updated i = entry basis i) := by
  let slot := UScalar.cast .Usize length
  have slotVal : slot.val = length.val := U32.cast_Usize_val_eq length
  obtain ⟨previous, subNormal, previousVal, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := slot) (y := 1#usize) (by simpa only [slotVal, show (1#usize).val = 1 by decide] using positive))
  have previousExact : previous.val = length.val - 1 := by simpa only [slotVal, show (1#usize).val = 1 by decide] using previousVal
  have read := read_normal basis previous (by change previous.val < 64; omega)
  have previousBound : previous.val < length.val := by omega
  rw [correct previous.val previousBound] at read
  let word := basisWord seed previous.val
  let updated := basis.set slot (basisNext word)
  have write := update_normal basis slot (basisNext word) (by change slot.val < 64; omega)
  obtain ⟨next, nextNormal, nextVal⟩ := u32_succ length (by omega)
  have nextWidth : next.val ≤ 64 := by omega
  have guard : length ≤ direction := active
  have bits : BulksketchFieldBinaryField.BITS - 1#u32 = Result.ok (63#u32) := by
    rw [BulksketchFieldBinaryField.BITS]
    rfl
  refine ⟨next, updated, ?_, nextVal, ?_, ?_⟩
  · have shr : (word >>> (63#u32 : U32)) = Result.ok ⟨(word.bv : BitVec 64) >>> (63 : Nat)⟩ := rfl
    have shl : (word <<< (1#i32 : I32)) = Result.ok ⟨(word.bv : BitVec 64) <<< (1 : Nat)⟩ := rfl
    simp only [Roots.trace_loop0.body, guard, ite_true, lift, bind_ok, show UScalar.cast .Usize length = slot from rfl, subNormal, read,
      bits, show basisWord seed previous.val = word from rfl, shr, shl, next_arithmetic, write, nextNormal, updated]
  · intro i below
    by_cases new : i = length.val
    · subst i
      have atSlot := entry_set_same basis slot (basisNext word) (by change slot.val < 64; omega)
      rw [slotVal] at atSlot
      have successor : length.val = previous.val + 1 := by omega
      change entry updated length.val = basisWord seed length.val
      rw [show entry updated length.val = basisNext word from atSlot]
      conv_rhs => rw [successor]
      rfl
    · have old : i < length.val := by omega
      rw [show entry updated i = entry basis i from entry_set_other basis slot i (basisNext word) (by omega)]
      exact correct i old
  · intro i other
    exact entry_set_other basis slot i (basisNext word) (by omega)

theorem basis_extension_refines : ActualBasisExtension := by
  intro seed direction length basis directionBound positive width correct
  suffices ∀ fuel (length : U32) (basis : Basis), 1 ≤ length.val → length.val ≤ 64 →
      cachePrefix seed basis length.val → direction.val + 1 - length.val = fuel →
      ∃ finalLength finalBasis,
        Roots.trace_loop0 gf64 direction length basis = .ok (finalLength, finalBasis) ∧
        finalLength.val = max length.val (direction.val + 1) ∧
        cachePrefix seed finalBasis finalLength.val ∧
        (∀ i, i < length.val ∨ finalLength.val ≤ i → entry finalBasis i = entry basis i)
    from this _ _ _ positive width correct rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro length basis positive width correct remaining
    by_cases active : length.val ≤ direction.val
    · obtain ⟨next, updated, step, nextVal, updatePrefix, frame⟩ :=
        extend_step seed direction length basis directionBound active positive correct
      have decrease : direction.val + 1 - next.val < fuel := by omega
      obtain ⟨finalLength, finalBasis, normal, finalVal, finalPrefix, recursiveFrame⟩ :=
        ih _ decrease next updated (by omega) (by omega) updatePrefix rfl
      refine ⟨finalLength, finalBasis, ?_, ?_, finalPrefix, ?_⟩
      · unfold Roots.trace_loop0 loop
        simp only [step, bind_ok]
        exact normal
      · rw [finalVal, Nat.max_eq_right (by omega : next.val ≤ direction.val + 1),
          Nat.max_eq_right (by omega : length.val ≤ direction.val + 1)]
      · intro i outside
        have finalBound : direction.val + 1 ≤ finalLength.val :=
          finalVal.symm ▸ Nat.le_max_right _ _
        have outsideNext : i < next.val ∨ finalLength.val ≤ i := by omega
        exact (recursiveFrame i outsideNext).trans (frame i (by omega))
    · have done : ¬ length ≤ direction := active
      refine ⟨length, basis, ?_, ?_, correct, fun _ _ => rfl⟩
      · unfold Roots.trace_loop0 loop
        simp only [Roots.trace_loop0.body, done, ite_false, bind_ok]
      · exact (Nat.max_eq_left (by omega : direction.val + 1 ≤ length.val)).symm

end BulksketchBridge.RootTrace
