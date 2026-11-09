import BulksketchBridge.BmPrice
import BulksketchBridge.StageCharge
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.CanonicalizePrice

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work

def ceilLog (ids : Nat) : Nat := if ids ≤ 1 then 0 else 1 + Nat.log 2 (ids - 1)

def units (ids : Usize) : Nat := ids.val * (ceilLog ids.val + 1)

private theorem leading_value (previous : Usize) (positive : 0 < previous.val) :
    (core.num.Usize.leading_zeros previous).val =
      System.Platform.numBits - Nat.log 2 previous.val - 1 := by
  have nonzero : previous.bv ≠ 0 := by
    intro eq
    have zero := congrArg BitVec.toNat eq
    rw [Usize.bv_toNat] at zero
    change previous.val = 0 at zero
    omega
  have zeros : BitVec.leadingZeros previous.bv =
      System.Platform.numBits - Nat.log 2 previous.val - 1 := by
    unfold BitVec.leadingZeros
    rw [ite_eq_right nonzero, Usize.bv_toNat]
  rw [← U32.bv_toNat]
  change (BitVec.ofNat 32 (BitVec.leadingZeros previous.bv)).toNat = _
  rw [BitVec.toNat_ofNat, zeros]
  exact Nat.mod_eq_of_lt (by have := System.Platform.numBits_le; omega)

private theorem source_bits_value : core.num.Usize.BITS.val = System.Platform.numBits := by
  unfold core.num.Usize.BITS UScalar.ofNat
  exact UScalar.ofNatCore_val_eq _

theorem ceilLog_refines (ids : Usize) :
    ∃ amount : U64, log2_ceil ids = .ok amount ∧
      amount.val = ceilLog ids.val ∧ amount.val ≤ 64 := by
  by_cases small : ids.val ≤ 1
  · have condition : ids ≤ 1#usize := small
    exact ⟨0#u64, by simp [log2_ceil, condition], by simp [ceilLog, small], by decide⟩
  · have condition : ¬ ids ≤ 1#usize := small
    obtain ⟨previous, normal, value⟩ := RawMulTable.normal_of_spec _ _
      (Usize.sub_spec (x := ids) (y := 1#usize) (by change 1 ≤ ids.val; omega))
    have pred : previous.val = ids.val - 1 := value.1
    have positive : 0 < previous.val := by omega
    have fits := previous.hBounds
    change previous.val < 2 ^ System.Platform.numBits at fits
    have logBound := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega : previous.val ≠ 0)).mpr fits
    have zeros := leading_value previous positive
    obtain ⟨bits, subNormal, subValue⟩ := RawMulTable.normal_of_spec _ _
      (U32.sub_spec (x := core.num.Usize.BITS) (y := core.num.Usize.leading_zeros previous)
        (by rw [zeros, source_bits_value]; omega))
    have exactBits : bits.val = 1 + Nat.log 2 previous.val := by
      rw [subValue.1, zeros, source_bits_value]
      omega
    let amount := core.convert.num.FromU64U32.from bits
    have amountVal : amount.val = bits.val := by
      change (UScalar.cast .U64 bits).val = bits.val
      rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt]
      change bits.val < 2 ^ 64
      have := System.Platform.numBits_le
      omega
    refine ⟨amount, ?_, ?_, ?_⟩
    · simp only [log2_ceil, condition, ite_false, normal, bind_ok, lift, subNormal]
      rfl
    · rw [amountVal, exactBits, pred, ceilLog, ite_eq_right small]
    · rw [amountVal, exactBits]
      have := System.Platform.numBits_le
      omega

theorem price_refines (ids : Usize) :
    WorkScheduleV1.cost (.Canonicalize ids) = .ok (checkedCost (units ids)) := by
  obtain ⟨word, converted, wordVal⟩ := number_refines ids
  obtain ⟨bits, logNormal, bitsVal, small⟩ := ceilLog_refines ids
  let width := U64.ofNatCore (bits.val + 1) (by change bits.val + 1 < 2 ^ 64; omega)
  have widthVal : width.val = bits.val + 1 := UScalar.ofNatCore_val_eq _
  have price1 : add bits 1#u64 = .ok (.Ok width) := by
    rw [BmPrice.add_refines]
    congr 1
    exact (checked_cost_ok_iff _ _).mpr ⟨by rw [U64.max_eq]; change bits.val + 1 ≤ _; omega, widthVal⟩
  have price2 : mul word width = .ok (checkedCost (units ids)) := by
    rw [mul_refines, wordVal, widthVal, bitsVal, units]
  simp only [WorkScheduleV1.cost, converted, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    logNormal, price1, price2]
  cases checkedCost (units ids) <;>
    simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem exact_charge {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : bulksketch.backend.contract.BulkKernels K F)
    (meter : bulksketch.types.WorkMeter) (ids : Usize) :
    bulksketch.decode.stages.Execution.charge field kernels meter (.Canonicalize ids) =
      .ok (StageCharge.chargeResult meter (checkedCost (units ids))) :=
  StageCharge.charge_refines_with_cost field kernels meter _ _ (price_refines ids)


end BulksketchBridge.CanonicalizePrice
