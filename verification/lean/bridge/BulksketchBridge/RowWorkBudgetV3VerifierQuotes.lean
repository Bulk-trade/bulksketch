import BulksketchBridge.BmPrice
import BulksketchBridge.AffineSelector

namespace BulksketchBridge.RootWorkBudget

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work
open core.result.Result.Insts
open AffineSelector (word word_val)

def originalVerifyUnits (capacity beta : Nat) : Nat :=
  (2 * beta + 3) * capacity + (beta + 1)

def rebuiltVerifyUnits (capacity budget beta : Nat) : Nat :=
  (3 * budget + 4) * capacity + (budget + (beta + 3))

private theorem number_word (source : Usize) (fits : source.val ≤ U64.max) :
    number source = .ok (.Ok (word source.val)) := by
  obtain ⟨result, call, value⟩ := number_refines source
  rw [call, show result = word source.val from UScalar.eq_of_val_eq (value.trans (word_val _ fits).symm)]

private theorem addNormal (left right : U64) (fits : left.val + right.val ≤ U64.max) :
    add left right = .ok (.Ok (word (left.val + right.val))) :=
  (BmPrice.add_refines left right).trans (congrArg Result.ok
    ((checked_cost_ok_iff ..).mpr ⟨fits, word_val _ fits⟩))

private theorem mulNormal (left right : U64) (fits : left.val * right.val ≤ U64.max) :
    mul left right = .ok (.Ok (word (left.val * right.val))) :=
  (mul_refines left right).trans (congrArg Result.ok
    ((checked_cost_ok_iff ..).mpr ⟨fits, word_val _ fits⟩))

private theorem addWords (left right : Nat) (fits : left + right ≤ U64.max) :
    add (word left) (word right) = .ok (.Ok (word (left + right))) := by
  have leftFits := (Nat.le_add_right ..).trans fits
  have rightFits := (Nat.le_add_left ..).trans fits
  simpa only [word_val left leftFits, word_val right rightFits] using
    addNormal (word left) (word right)
      (by rw [word_val left leftFits, word_val right rightFits]; exact fits)

private theorem mulWords (left right : Nat) (leftFits : left ≤ U64.max) (rightFits : right ≤ U64.max)
    (fits : left * right ≤ U64.max) :
    mul (word left) (word right) = .ok (.Ok (word (left * right))) := by
  simpa only [word_val left leftFits, word_val right rightFits] using
    mulNormal (word left) (word right)
      (by rw [word_val left leftFits, word_val right rightFits]; exact fits)

def ActualNativeV3VerifierQuotes : Prop :=
  ∀ (capacity budget beta : Usize),
    capacity.val ≤ 65535 → budget.val ≤ 65535 → beta.val ≤ 65535 →
    WorkScheduleV1.cost (.Verify capacity beta) =
        .ok (.Ok (word (originalVerifyUnits capacity.val beta.val))) ∧
    WorkScheduleV1.cost (.VerifyLfsr capacity beta budget) =
        .ok (.Ok (word (rebuiltVerifyUnits capacity.val budget.val beta.val))) ∧
    originalVerifyUnits capacity.val beta.val + 2337 ≤ U64.max ∧
    rebuiltVerifyUnits capacity.val budget.val beta.val ≤ U64.max

theorem native_v3_verifier_quotes : ActualNativeV3VerifierQuotes := by
  intro capacity budget beta capBound budgetBound betaBound
  let c := capacity.val
  let d := budget.val
  let b := beta.val
  have cBound : c ≤ 65535 := capBound
  have dBound : d ≤ 65535 := budgetBound
  have bBound : b ≤ 65535 := betaBound
  have cFits : c ≤ U64.max := by rw [U64.max_eq]; omega
  have dFits : d ≤ U64.max := by rw [U64.max_eq]; omega
  have bFits : b ≤ U64.max := by rw [U64.max_eq]; omega
  have originalProduct : (2 * b + 3) * c ≤ 131073 * 65535 :=
    Nat.mul_le_mul (show 2 * b + 3 ≤ 131073 by omega) cBound
  have rebuiltProduct : (3 * d + 4) * c ≤ 196609 * 65535 :=
    Nat.mul_le_mul (show 3 * d + 4 ≤ 196609 by omega) cBound
  have originalTotal : originalVerifyUnits c b + 2337 ≤ U64.max := by
    unfold originalVerifyUnits
    rw [U64.max_eq]
    omega
  have rebuiltTotal : rebuiltVerifyUnits c d b ≤ U64.max := by
    unfold rebuiltVerifyUnits
    rw [U64.max_eq]
    omega
  refine ⟨?_, ?_, originalTotal, rebuiltTotal⟩
  · have twice : mul 2#u64 (word b) = .ok (.Ok (word (2 * b))) := by
      have result := mulWords 2 b (by rw [U64.max_eq]; decide) bFits (by rw [U64.max_eq]; omega)
      exact result
    have width : add (word (2 * b)) 3#u64 = .ok (.Ok (word (2 * b + 3))) :=
      addWords (2 * b) 3 (by rw [U64.max_eq]; omega)
    have terms := mulWords (2 * b + 3) c (by rw [U64.max_eq]; omega) cFits (by rw [U64.max_eq]; omega)
    have outputs : add (word b) 1#u64 = .ok (.Ok (word (b + 1))) :=
      addWords b 1 (by rw [U64.max_eq]; omega)
    have total := addWords ((2 * b + 3) * c) (b + 1) (by unfold originalVerifyUnits at originalTotal; omega)
    dsimp only [b, c] at twice width terms outputs total
    simp only [WorkScheduleV1.cost, number_word capacity cFits, number_word beta bFits,
      bind_ok, CoreOpsTry.branch, twice, width, terms, outputs, total] <;> rfl
  · have triple : mul 3#u64 (word d) = .ok (.Ok (word (3 * d))) := by
      have result := mulWords 3 d (by rw [U64.max_eq]; decide) dFits (by rw [U64.max_eq]; omega)
      exact result
    have width : add (word (3 * d)) 4#u64 = .ok (.Ok (word (3 * d + 4))) :=
      addWords (3 * d) 4 (by rw [U64.max_eq]; omega)
    have terms := mulWords (3 * d + 4) c (by rw [U64.max_eq]; omega) cFits (by rw [U64.max_eq]; omega)
    have outputs : add (word b) 3#u64 = .ok (.Ok (word (b + 3))) :=
      addWords b 3 (by rw [U64.max_eq]; omega)
    have exactCandidates := addWords d (b + 3) (by rw [U64.max_eq]; omega)
    have total := addWords ((3 * d + 4) * c) (d + (b + 3)) rebuiltTotal
    dsimp only [b, c, d] at triple width terms outputs exactCandidates total
    simp only [WorkScheduleV1.cost, number_word capacity cFits, number_word beta bFits, number_word budget dFits,
      bind_ok, CoreOpsTry.branch, triple, width, terms, outputs, exactCandidates, total] <;> rfl

#print axioms native_v3_verifier_quotes

end BulksketchBridge.RootWorkBudget
