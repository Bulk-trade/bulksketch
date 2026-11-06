import BulksketchBridge.FrobeniusConstMath

namespace BulksketchBridge.FrobeniusConst

open Aeneas Aeneas.Std

def counter (count : Nat) : I32 := ⟨BitVec.ofNat 32 count⟩

theorem counter_value (count : Nat) (bound : count ≤ 256) :
    (counter count).val = (count : Int) := by
  have fits : count < 2 ^ 32 := by omega
  have unsigned : (BitVec.ofNat 32 count).toNat = count := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  change (BitVec.ofNat 32 count).toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [unsigned]; omega), unsigned]

private theorem normal_of_spec {α : Type} (program : Result α) (post : α → Prop)
    (correct : program ⦃ post ⦄) : ∃ output, program = Result.ok output ∧ post output := by
  cases program using Result.cases <;> simp_all

theorem counter_add (count : Nat) (bound : count ≤ 128) :
    counter count + 1#i32 = Result.ok (counter (count + 1)) := by
  have current := counter_value count (by omega)
  obtain ⟨output, normal, meaning⟩ := normal_of_spec _ _
    (I32.add_spec (x := counter count) (y := 1#i32) (by scalar_tac) (by scalar_tac))
  have equal : output = counter (count + 1) := by
    apply IScalar.eq_of_val_eq
    rw [counter_value _ (by omega), meaning, current]
    rfl
  exact normal.trans (congrArg Result.ok equal)

theorem counter_double (count : Nat) (bound : count ≤ 64) :
    2#i32 * counter count = Result.ok (counter (2 * count)) := by
  have current := counter_value count (by omega)
  obtain ⟨output, normal, meaning⟩ := normal_of_spec _ _
    (I32.mul_spec (x := 2#i32) (y := counter count) (by scalar_tac) (by scalar_tac))
  have equal : output = counter (2 * count) := by
    apply IScalar.eq_of_val_eq
    rw [counter_value _ (by omega), meaning, current]
    simp
  exact normal.trans (congrArg Result.ok equal)

theorem shift_normal {ty : UScalarTy} (input : UScalar ty) (count : Nat)
    (bound : count < ty.numBits) (small : count ≤ 256) :
    input <<< counter count = Result.ok (⟨input.bv <<< count⟩ : UScalar ty) := by
  have current := counter_value count small
  obtain ⟨output, normal, _, bits⟩ := normal_of_spec _ _
    (UScalar.ShiftLeft_IScalar_spec input (counter count) (UScalar.size ty)
      (by omega) (by omega) rfl)
  have equal : output = (⟨input.bv <<< count⟩ : UScalar ty) := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    simpa only [IScalar.toNat, current, Int.toNat_natCast] using bits
  exact normal.trans (congrArg Result.ok equal)

theorem masked_single_bit {width : Nat} (input : BitVec width) (index : Nat)
    (bound : index < width) :
    (input &&& ((1 : BitVec width) <<< index)) ≠ 0 ↔ input.getLsbD index = true := by
  have mask : input &&& ((1 : BitVec width) <<< index) =
      if input.getLsbD index then ((1 : BitVec width) <<< index) else 0 := by
    simpa only [BitVec.twoPow_eq, BitVec.ofNat_eq_ofNat] using BitVec.and_twoPow input index
  have nonzero : ((1 : BitVec width) <<< index) ≠ 0 := by
    intro equal
    have bit := congrArg (fun word : BitVec width => word.getLsbD index) equal
    rw [single_bit _ _ (by omega)] at bit
    simp [bound] at bit
  rw [mask]
  split_ifs with selected
  · exact ⟨fun _ => selected, fun _ => nonzero⟩
  · constructor
    · intro impossible
      exact False.elim (impossible rfl)
    · intro impossible
      exact False.elim (selected impossible)

theorem spread_body (input : U64) (count : Nat) (bound : count < 64) :
    bulksketch.field.frobenius.square_loop0.body input
      (⟨spreadPrefix input.bv count⟩ : U128) (counter count) =
        Result.ok (ControlFlow.cont
          ((⟨spreadPrefix input.bv (count + 1)⟩ : U128), counter (count + 1))) := by
  have active : counter count < 64#i32 := by
    rw [IScalar.lt_equiv, counter_value count (by omega)]
    change (count : Int) < 64
    omega
  have maskTest :
      (input &&& (⟨(1 : BitVec 64) <<< count⟩ : U64)) ≠ 0#u64 ↔
        input.bv.getLsbD count = true := by
    rw [ne_eq, UScalar.eq_equiv_bv_eq]
    exact masked_single_bit input.bv count bound
  simp only [BitVec.ofNat_eq_ofNat] at maskTest
  simp only [bulksketch.field.frobenius.square_loop0.body, active, ite_true,
    shift_normal (1#u64) count bound (by omega), lift, bind_ok, bne_iff_ne,
    U64.ofNat_bv, U128.ofNat_bv, UScalarTy.U64_numBits_eq, UScalarTy.U128_numBits_eq,
    maskTest, counter_double count (by omega),
    shift_normal (1#u128) (2 * count) (by change 2 * count < 128; omega) (by omega),
    counter_add count (by omega)]
  cases selected : input.bv.getLsbD count <;>
    simp only [selected, Bool.false_eq_true, ite_false, ite_true, bind_ok,
      spreadPrefix, BitVec.ofNat_eq_ofNat, BitVec.xor_zero]
  all_goals rfl

theorem spread_loop (input : U64) (count : Nat) (bound : count ≤ 64) :
    bulksketch.field.frobenius.square_loop0 input
      (⟨spreadPrefix input.bv count⟩ : U128) (counter count) =
        Result.ok (⟨spreadPrefix input.bv 64⟩ : U128) := by
  suffices ∀ remaining count, count ≤ 64 → 64 - count = remaining →
      bulksketch.field.frobenius.square_loop0 input
        (⟨spreadPrefix input.bv count⟩ : U128) (counter count) =
          Result.ok (⟨spreadPrefix input.bv 64⟩ : U128) from
    this (64 - count) count bound rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining inductionHypothesis =>
    intro count bound remainingEq
    by_cases active : count < 64
    · unfold bulksketch.field.frobenius.square_loop0
      unfold loop
      dsimp only
      rw [spread_body input count active]
      simp only [bind_ok]
      exact inductionHypothesis (64 - (count + 1)) (by omega) (count + 1) (by omega) rfl
    · have done : count = 64 := by omega
      subst count
      unfold bulksketch.field.frobenius.square_loop0
      unfold loop
      dsimp only
      have terminal : bulksketch.field.frobenius.square_loop0.body input
          (⟨spreadPrefix input.bv 64⟩ : U128) (counter 64) =
            Result.ok (ControlFlow.done (⟨spreadPrefix input.bv 64⟩ : U128)) := by rfl
      rw [terminal]
      simp only [bind_ok]

theorem counter_sub (count amount : Nat) (countBound : count ≤ 128)
    (amountBound : amount ≤ count) :
    counter count - counter amount = Result.ok (counter (count - amount)) := by
  have countValue := counter_value count (by omega)
  have amountValue := counter_value amount (by omega)
  obtain ⟨output, normal, meaning⟩ := normal_of_spec _ _
    (I32.sub_spec (x := counter count) (y := counter amount) (by scalar_tac) (by scalar_tac))
  have equal : output = counter (count - amount) := by
    apply IScalar.eq_of_val_eq
    rw [counter_value _ (by omega), meaning, countValue, amountValue]
    omega
  exact normal.trans (congrArg Result.ok equal)

theorem division_body (input : BitVec 128) (count : Nat) (bound : count < 64) :
    bulksketch.field.frobenius.square_loop1.body (⟨polynomial⟩ : U128)
      (⟨divisionPrefix input count⟩ : U128) (counter (128 - count)) =
        Result.ok (ControlFlow.cont
          ((⟨divisionPrefix input (count + 1)⟩ : U128), counter (128 - (count + 1)))) := by
  have active : counter (128 - count) > 64#i32 := by
    change (64 : Int) < (counter (128 - count)).val
    rw [counter_value _ (by omega)]
    omega
  have decrement : counter (128 - count) - 1#i32 = Result.ok (counter (127 - count)) := by
    have one : (1#i32) = counter 1 := by rfl
    rw [one]
    rw [counter_sub _ _ (by omega) (by omega)]
    congr 2
    omega
  have subtract64 : counter (127 - count) - 64#i32 = Result.ok (counter (63 - count)) := by
    have sixtyFour : (64#i32) = counter 64 := by rfl
    rw [sixtyFour]
    rw [counter_sub _ _ (by omega) (by omega)]
    congr 2
    omega
  have maskTest :
      ((⟨divisionPrefix input count⟩ : U128) &&&
        (⟨(1 : BitVec 128) <<< (127 - count)⟩ : U128)) ≠ 0#u128 ↔
        (divisionPrefix input count).getLsbD (127 - count) = true := by
    rw [ne_eq, UScalar.eq_equiv_bv_eq]
    exact masked_single_bit _ _ (by change 127 - count < 128; omega)
  simp only [BitVec.ofNat_eq_ofNat] at maskTest
  simp only [bulksketch.field.frobenius.square_loop1.body, active, ite_true,
    decrement, bind_ok, shift_normal (1#u128) (127 - count)
      (by change 127 - count < 128; omega) (by omega), lift, bne_iff_ne,
    U128.ofNat_bv, UScalarTy.U128_numBits_eq, maskTest, subtract64,
    shift_normal (⟨polynomial⟩ : U128) (63 - count)
      (by change 63 - count < 128; omega) (by omega)]
  have next : 128 - (count + 1) = 127 - count := by omega
  have shifted : 127 - count - 64 = 63 - count := by omega
  rw [next]
  cases selected : (divisionPrefix input count).getLsbD (127 - count) <;>
    simp only [selected, Bool.false_eq_true, ite_false, ite_true,
      divisionPrefix, divisionStep, shifted]
  all_goals rfl

theorem division_loop (input : BitVec 128) (count : Nat) (bound : count ≤ 64) :
    bulksketch.field.frobenius.square_loop1
      (⟨divisionPrefix input count⟩ : U128) (counter (128 - count)) (⟨polynomial⟩ : U128) =
        Result.ok (⟨divisionPrefix input 64⟩ : U128) := by
  suffices ∀ remaining count, count ≤ 64 → 64 - count = remaining →
      bulksketch.field.frobenius.square_loop1
        (⟨divisionPrefix input count⟩ : U128) (counter (128 - count)) (⟨polynomial⟩ : U128) =
          Result.ok (⟨divisionPrefix input 64⟩ : U128) from
    this (64 - count) count bound rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining inductionHypothesis =>
    intro count bound remainingEq
    by_cases active : count < 64
    · unfold bulksketch.field.frobenius.square_loop1
      unfold loop
      dsimp only
      rw [division_body input count active]
      simp only [bind_ok]
      exact inductionHypothesis (64 - (count + 1)) (by omega) (count + 1) (by omega) rfl
    · have done : count = 64 := by omega
      subst count
      unfold bulksketch.field.frobenius.square_loop1
      unfold loop
      dsimp only
      have terminal : bulksketch.field.frobenius.square_loop1.body (⟨polynomial⟩ : U128)
          (⟨divisionPrefix input 64⟩ : U128) (counter (128 - 64)) =
            Result.ok (ControlFlow.done (⟨divisionPrefix input 64⟩ : U128)) := by rfl
      rw [terminal]
      simp only [bind_ok]

end BulksketchBridge.FrobeniusConst
