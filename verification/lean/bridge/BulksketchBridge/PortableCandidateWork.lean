import BulksketchBridge.NativeTraceRecoveredFinish
import BulksketchBridge.RowWorkBudgetV3Complete

namespace BulksketchBridge.PortableDecoder

open Aeneas.Std WorkSchedule CandidateOuter Deflation
open bulksketch.types
open AffineSelector (word word_val)

private theorem checked_word (n : Nat) (fits : n ≤ U64.max) :
    checkedCost n = .Ok (word n) :=
  (checked_cost_ok_iff _ _).mpr ⟨fits, word_val _ fits⟩

/-- The candidate scan's intermediate checked products fit whenever its
complete natural charge fits. -/
theorem paid_candidate_price (degree inputs : Usize) (admitted : degree.val ≤ 65535)
    (fits : 2 * inputs.val * (degree.val + 1) ≤ U64.max) :
    candidateCost degree inputs = .Ok (word (2 * inputs.val * (degree.val + 1))) := by
  have countFits : 2 * inputs.val ≤ U64.max :=
    (Nat.le_mul_of_pos_right _ (by omega)).trans fits
  have widthFits : degree.val + 1 ≤ U64.max := by rw [U64.max_eq]; omega
  simp only [candidateCost, checked_word _ countFits, checked_word _ widthFits, word_val _ countFits,
    word_val _ widthFits, checked_word _ fits]

theorem charge_checked (meter : WorkMeter) (amount : Nat)
    (live : meter.exhausted = false) (room : meter.used.val + amount ≤ meter.limit.val) :
    ∃ paid, StageCharge.chargeResult meter (checkedCost amount) = (.Ok (), paid) ∧
      paid.used.val = meter.used.val + amount ∧ paid.limit = meter.limit ∧ paid.exhausted = false := by
  have fits : amount ≤ U64.max := by
    have limitFits := meter.limit.le_max
    rw [U64.max_eq] at *
    omega
  have amountVal := word_val amount fits
  obtain ⟨paid, charged, used, limit, active⟩ :=
    WorkMeter.native_work_meter_paid meter (word amount) live (by rwa [amountVal])
  rw [StageCharge.meter_charge_refines] at charged
  exact ⟨paid, by rw [checked_word _ fits]; exact Result.ok_injective charged,
    by rwa [amountVal] at used, limit, active⟩

/-- Exact payment for the original two steps before root traversal. -/
theorem candidate_deflate_paid (degree candidates : Usize) (meter : WorkMeter)
    (admitted : degree.val ≤ 65535) (live : meter.exhausted = false)
    (room : meter.used.val + 2 * candidates.val * (degree.val + 1) +
      deflateUnits degree ≤ meter.limit.val) :
    let candidate := StageCharge.chargeResult meter (candidateCost degree candidates)
    candidate.1 = .Ok () ∧
    ∃ paid, StageCharge.chargeResult candidate.2 (deflateCost degree) = (.Ok (), paid) ∧
      paid.used.val = meter.used.val + 2 * candidates.val * (degree.val + 1) + deflateUnits degree ∧
      paid.limit = meter.limit ∧ paid.exhausted = false := by
  dsimp only
  let units := 2 * candidates.val * (degree.val + 1)
  have enough : meter.used.val + units + deflateUnits degree ≤ meter.limit.val := room
  have fits : units ≤ U64.max := by
    have limitFits := meter.limit.le_max
    rw [U64.max_eq] at *
    omega
  have price : candidateCost degree candidates = checkedCost units :=
    (paid_candidate_price degree candidates admitted fits).trans (checked_word _ fits).symm
  obtain ⟨candidate, charged, used, limit, active⟩ := charge_checked meter units live (by omega)
  rw [price, charged]
  obtain ⟨final, deflated, finalUsed, finalLimit, finalLive⟩ :=
    charge_checked candidate (deflateUnits degree) active (by rw [used, limit]; exact enough)
  exact ⟨rfl, final, deflated, by rw [finalUsed, used], finalLimit.trans limit, finalLive⟩

end BulksketchBridge.PortableDecoder
