import BulksketchProofs.Resource.WorkMeterSpec
import Init.Data.UInt.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Finite-width work-meter model

This handwritten model follows `bulksketch/src/types.rs:272-301` at revision
`0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`. The model uses actual `UInt64`
state and rejects sums outside its 64-bit range before conversion.

The theorems below concern this Lean model. A refinement bridge from the Rust
source, compiler, and machine execution is a separate, currently unproved task.
-/

namespace BulksketchProofs.Resource

/-- A non-overflowing machine addition equals the exact natural-number sum. -/
theorem toNat_add_of_no_overflow (a b : UInt64)
    (h : a.toNat + b.toNat < UInt64.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

/-- Overflow is detected at the first unrepresentable sum, exactly 2^64. -/
theorem checkedAdd64_none_iff (a b : UInt64) :
    checkedAdd64 a b = none ↔ UInt64.size ≤ a.toNat + b.toNat := by
  unfold checkedAdd64
  split <;> simp_all <;> omega

/-- A present checked result has the exact sum, without modular wraparound. -/
theorem checkedAdd64_some_iff (a b value : UInt64) :
    checkedAdd64 a b = some value ↔
      a.toNat + b.toNat < UInt64.size ∧ value.toNat = a.toNat + b.toNat := by
  by_cases h : a.toNat + b.toNat < UInt64.size
  · simp only [checkedAdd64, h, ↓reduceIte, Option.some.injEq, true_and]
    rw [← toNat_add_of_no_overflow a b h]
    constructor
    · intro he
      rw [he]
    · intro he
      exact UInt64.toNat_inj.mp he.symm
  · simp [checkedAdd64, h]

/-- A simpler complete specification of the Option-based state transition. -/
theorem WorkMeter.charge_spec (meter : WorkMeter) (amount : UInt64) :
    meter.charge amount =
      if meter.exhausted = false ∧ meter.used.toNat + amount.toNat ≤ meter.limit.toNat then
        ({ meter with used := meter.used + amount }, true)
      else
        ({ meter with exhausted := true }, false) := by
  cases he : meter.exhausted with
  | true => simp [WorkMeter.charge, he]
  | false =>
    by_cases hs : meter.used.toNat + amount.toNat < UInt64.size
    · have ha := toNat_add_of_no_overflow meter.used amount hs
      simp [WorkMeter.charge, he, checkedAdd64, hs, ha]
    · have hl : ¬ meter.used.toNat + amount.toNat ≤ meter.limit.toNat := by
        have := meter.limit.toNat_lt_size
        omega
      simp [WorkMeter.charge, he, checkedAdd64, hs, hl]

/-- Success requires a live meter and a representable sum at or below its limit. -/
theorem WorkMeter.charge_success_iff (meter : WorkMeter) (amount : UInt64) :
    (meter.charge amount).2 = true ↔
      meter.exhausted = false ∧ meter.used.toNat + amount.toNat ≤ meter.limit.toNat := by
  rw [WorkMeter.charge_spec]
  split <;> simp_all

theorem WorkMeter.charge_eq_of_success (meter : WorkMeter) (amount : UInt64)
    (h : (meter.charge amount).2 = true) :
    meter.charge amount = ({ meter with used := meter.used + amount }, true) := by
  rw [WorkMeter.charge_spec]
  simp [(WorkMeter.charge_success_iff meter amount).mp h]

theorem WorkMeter.charge_eq_of_failure (meter : WorkMeter) (amount : UInt64)
    (h : (meter.charge amount).2 = false) :
    meter.charge amount = ({ meter with exhausted := true }, false) := by
  rw [WorkMeter.charge_spec]
  have hn : ¬ (meter.exhausted = false ∧
      meter.used.toNat + amount.toNat ≤ meter.limit.toNat) := by
    intro hs
    have := (WorkMeter.charge_success_iff meter amount).mpr hs
    simp [h] at this
  simp [hn]

/-- Failure does not consume the denied charge. -/
theorem WorkMeter.used_unchanged_on_failure (meter : WorkMeter) (amount : UInt64)
    (h : (meter.charge amount).2 = false) :
    (meter.charge amount).1.used = meter.used := by
  rw [meter.charge_eq_of_failure amount h]

/-- Failure sets the sticky exhausted flag. -/
theorem WorkMeter.exhausted_on_failure (meter : WorkMeter) (amount : UInt64)
    (h : (meter.charge amount).2 = false) :
    (meter.charge amount).1.exhausted = true := by
  rw [meter.charge_eq_of_failure amount h]

/-- An exhausted meter rejects every charge, including zero. -/
theorem WorkMeter.exhausted_sticky (meter : WorkMeter) (amount : UInt64)
    (h : meter.exhausted = true) :
    meter.charge amount = (meter, false) := by
  cases meter
  simp_all [WorkMeter.charge]

theorem WorkMeter.limit_unchanged (meter : WorkMeter) (amount : UInt64) :
    (meter.charge amount).1.limit = meter.limit := by
  rw [meter.charge_spec]
  split <;> rfl

/-- Successful used accounting is exact natural addition of finite machine words. -/
theorem WorkMeter.used_on_success (meter : WorkMeter) (amount : UInt64)
    (h : (meter.charge amount).2 = true) :
    (meter.charge amount).1.used.toNat = meter.used.toNat + amount.toNat := by
  have hs := (WorkMeter.charge_success_iff meter amount).mp h
  have hb : meter.used.toNat + amount.toNat < UInt64.size := by
    have := meter.limit.toNat_lt_size
    omega
  rw [meter.charge_eq_of_success amount h]
  exact toNat_add_of_no_overflow meter.used amount hb

/-- A successful operation cannot leave its final used value above the limit. -/
theorem WorkMeter.bounded_on_success (meter : WorkMeter) (amount : UInt64)
    (h : (meter.charge amount).2 = true) :
    (meter.charge amount).1.Bounded := by
  have hs := (WorkMeter.charge_success_iff meter amount).mp h
  unfold WorkMeter.Bounded
  rw [meter.used_on_success amount h, meter.limit_unchanged amount]
  exact hs.2

theorem WorkMeter.new_bounded (limit : UInt64) : (WorkMeter.new limit).Bounded := by
  simp [WorkMeter.new, WorkMeter.Bounded]

/-- The finite-width invariant is preserved even when a charge is denied. -/
theorem WorkMeter.bounded_preserved (meter : WorkMeter) (amount : UInt64)
    (h : meter.Bounded) : (meter.charge amount).1.Bounded := by
  cases hs : (meter.charge amount).2 with
  | false =>
    unfold WorkMeter.Bounded at h ⊢
    rw [meter.used_unchanged_on_failure amount hs, meter.limit_unchanged amount]
    exact h
  | true => exact meter.bounded_on_success amount hs

/-- Reaching the exact limit is permitted. -/
theorem WorkMeter.exact_boundary (meter : WorkMeter) (amount : UInt64)
    (he : meter.exhausted = false)
    (hs : meter.used.toNat + amount.toNat = meter.limit.toNat) :
    meter.charge amount = ({ meter with used := meter.limit }, true) := by
  have hk : (meter.charge amount).2 = true :=
    (meter.charge_success_iff amount).mpr ⟨he, Nat.le_of_eq hs⟩
  rw [meter.charge_eq_of_success amount hk]
  have hsum : meter.used.toNat + amount.toNat < UInt64.size := by
    rw [hs]
    exact meter.limit.toNat_lt_size
  have hadd : meter.used + amount = meter.limit := UInt64.toNat_inj.mp (by
    rw [toNat_add_of_no_overflow meter.used amount hsum, hs])
  rw [hadd]

/-- A finite, non-overflowing sum above the policy limit still fails. -/
theorem WorkMeter.over_limit (meter : WorkMeter) (amount : UInt64)
    (h : meter.limit.toNat < meter.used.toNat + amount.toNat) :
    meter.charge amount = ({ meter with exhausted := true }, false) := by
  rw [meter.charge_spec]
  have hn : ¬ meter.used.toNat + amount.toNat ≤ meter.limit.toNat := by omega
  simp [hn]

/-- Overflow cannot wrap the counter back below the limit. -/
theorem WorkMeter.overflow_rejected (meter : WorkMeter) (amount : UInt64)
    (h : UInt64.size ≤ meter.used.toNat + amount.toNat) :
    meter.charge amount = ({ meter with exhausted := true }, false) := by
  apply meter.over_limit amount
  have := meter.limit.toNat_lt_size
  omega

/-- Zero is accepted without changing a live, well-formed meter. -/
theorem WorkMeter.zero_charge (meter : WorkMeter)
    (he : meter.exhausted = false) (hb : meter.Bounded) :
    meter.charge 0 = (meter, true) := by
  have hs : (meter.charge 0).2 = true := (meter.charge_success_iff 0).mpr (by
    simpa [WorkMeter.Bounded] using And.intro he hb)
  rw [meter.charge_eq_of_success 0 hs]
  simp

/-- Every successful sequence records the exact sum, not a modular sum. -/
theorem WorkMeter.successful_charges_sum (meter : WorkMeter) (amounts : List UInt64)
    (h : (meter.chargeAll amounts).2 = true) :
    (meter.chargeAll amounts).1.used.toNat =
      meter.used.toNat + (amounts.map UInt64.toNat).sum := by
  induction amounts generalizing meter with
  | nil => simp [WorkMeter.chargeAll]
  | cons amount rest ih =>
    cases hs : (meter.charge amount).2 with
    | false => simp [WorkMeter.chargeAll, hs] at h
    | true =>
      simp only [WorkMeter.chargeAll, hs, ↓reduceIte] at h ⊢
      rw [ih (meter.charge amount).1 h, meter.used_on_success amount hs]
      simp [Nat.add_assoc]

/-- A sequence preserves bounded accounting whether it stops early or completes. -/
theorem WorkMeter.chargeAll_bounded (meter : WorkMeter) (amounts : List UInt64)
    (h : meter.Bounded) : (meter.chargeAll amounts).1.Bounded := by
  induction amounts generalizing meter with
  | nil => exact h
  | cons amount rest ih =>
    have hb := meter.bounded_preserved amount h
    cases hs : (meter.charge amount).2 with
    | false => simpa [WorkMeter.chargeAll, hs] using hb
    | true => simpa [WorkMeter.chargeAll, hs] using ih (meter.charge amount).1 hb

/-- Once a sequence has failed, any following single charge remains rejected. -/
theorem WorkMeter.failure_stays_failed (meter : WorkMeter) (first second : UInt64)
    (h : (meter.charge first).2 = false) :
    ((meter.charge first).1.charge second).2 = false := by
  rw [(meter.charge first).1.exhausted_sticky second (meter.exhausted_on_failure first h)]

end BulksketchProofs.Resource
