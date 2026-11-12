import Arithmetic.AffineSolveMapGenerated
import BulksketchBridge.FrobeniusConst
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.AffineSolveMap

open Aeneas Aeneas.Std Result ControlFlow
open BulksketchProofs.Field FrobeniusConst
open bulksketch.decode.affine

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem extract_one (word : BitVec 64) (index : Nat) :
    (word >>> index) &&& 1 = (if word.getLsbD index then 1 else 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bound
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  by_cases low : bit = 0
  · subst bit
    cases word.getLsbD index <;> simp
  · have off : (1 : BitVec 64).getLsbD bit = false := by
      simp [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt (by
          have positive : 0 < bit := by omega
          have gt := Nat.pow_lt_pow_right (a := 2) (by decide) positive
          exact gt)]
    rw [off, Bool.and_false]
    split <;> simp_all

private theorem shift_right_normal (input : U64) (count : Nat) (active : count < 64) :
    (input >>> counter count : Result U64) = .ok (⟨input.bv >>> count⟩ : U64) := by
  have countVal := counter_value count (by omega)
  obtain ⟨output, normal, _, bits⟩ := RawMulTable.normal_of_spec _ _
    (U64.ShiftRight_IScalar_spec input (counter count) (by omega) (by omega))
  have equal : output = (⟨input.bv >>> count⟩ : U64) := by
    apply U64.bv_eq_imp_eq
    simpa only [IScalar.toNat, countVal, Int.toNat_natCast] using bits
  exact normal.trans (congrArg Result.ok equal)

theorem affine_spread_body (input : U64) (count : Nat) (active : count < 64) :
    square_column_loop0.body input (⟨spreadPrefix input.bv count⟩ : U128) (counter count) =
      .ok (.cont ((⟨spreadPrefix input.bv (count + 1)⟩ : U128), counter (count + 1))) := by
  have guard : counter count < 64#i32 := by
    rw [IScalar.lt_equiv, counter_value _ (by omega)]
    change (count : Int) < 64
    omega
  have bit : ((⟨input.bv >>> count⟩ : U64) &&& 1#u64) =
      (if input.bv.getLsbD count then 1#u64 else 0#u64) := by
    apply U64.bv_eq_imp_eq
    change (input.bv >>> count) &&& 1 = _
    rw [extract_one]
    split <;> rfl
  have shiftBound : 2 * count < UScalarTy.U128.numBits := by
    change 2 * count < 128
    omega
  simp only [square_column_loop0.body, guard, ite_true, shift_right_normal input count active,
    bind_ok, lift, bit, counter_double count (by omega), counter_add count (by omega)]
  cases selected : input.bv.getLsbD count <;>
    simp only [selected, ite_true, Bool.false_eq_true, ite_false,
      shift_normal _ (2 * count) shiftBound (by omega), bind_ok, spreadPrefix]
  · apply congrArg Result.ok
    congr 2
    apply U128.bv_eq_imp_eq
    simp only [UScalar.cast_bv_eq]
    simp
  · rfl

theorem affine_spread_loop (input : U64) (count : Nat) (bounded : count ≤ 64) :
    square_column_loop0 input (⟨spreadPrefix input.bv count⟩ : U128) (counter count) =
      .ok (⟨spreadPrefix input.bv 64⟩ : U128) := by
  suffices ∀ remaining count, count ≤ 64 → 64 - count = remaining →
    square_column_loop0 input (⟨spreadPrefix input.bv count⟩ : U128) (counter count) =
      .ok (⟨spreadPrefix input.bv 64⟩ : U128) by
    exact this (64 - count) count bounded rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro count bounded remainingEq
    by_cases active : count < 64
    · unfold square_column_loop0 loop
      dsimp only
      rw [affine_spread_body input count active]
      simp only [bind_ok]
      exact ih (64 - (count + 1)) (by omega) (count + 1) (by omega) rfl
    · have last : count = 64 := by omega
      subst count
      unfold square_column_loop0 loop
      have stop : ¬ counter 64 < 64#i32 := by
        rw [IScalar.lt_equiv, counter_value 64 (by decide)]
        change ¬ (64 : Int) < 64
        decide
      simp only [square_column_loop0.body, stop, ite_false, bind_ok]

/-- The affine table's separate native squaring body computes the exact
same GF64 square as the canonical polynomial square. -/
def ActualSquareColumn : Prop :=
  ∀ input : U64, square_column input = .ok (⟨Period.squareWord input.bv⟩ : U64)

theorem square_column_refines : ActualSquareColumn := by
  intro input
  have spread := affine_spread_loop input 0 (by decide)
  have division := division_loop (spreadPrefix input.bv 64) 0 (by decide)
  change square_column_loop0 input 0#u128 0#i32 = _ at spread
  change square_column_loop1
      (⟨spreadPrefix input.bv 64⟩ : U128) 128#i32 (⟨polynomial⟩ : U128) = _ at division
  have shift64 : 1#u128 <<< 64#i32 = Result.ok (⟨(1 : BitVec 128) <<< 64⟩ : U128) := by
    have normal := shift_normal (1#u128) 64 (by change 64 < 128; decide) (by decide)
    have literal : counter 64 = 64#i32 := by rfl
    rw [literal] at normal
    simpa only [U128.ofNat_bv, UScalarTy.U128_numBits_eq, BitVec.ofNat_eq_ofNat] using normal
  have polynomialValue :
      ((⟨(1 : BitVec 128) <<< 64⟩ : U128) ||| 27#u128) = (⟨polynomial⟩ : U128) := by
    decide +kernel
  simp only [square_column, spread, shift64, lift, bind_ok, polynomialValue, division]
  apply congrArg Result.ok
  apply U64.bv_eq_imp_eq
  rw [UScalar.cast_bv_eq]
  change (divisionPrefix (spreadPrefix input.bv 64) 64).setWidth 64 = _
  rw [spreadPrefix_complete, division_square_complete]
  simp

#print axioms square_column_refines

end BulksketchBridge.AffineSolveMap
