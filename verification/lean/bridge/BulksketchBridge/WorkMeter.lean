import BulksketchBridge.WorkMeterSpec
import Workmeter.Funs
import BulksketchProofs.Resource.WorkMeter

/-!
# Generated-body WorkMeter refinement

The function bodies imported from `Workmeter.Funs` are copied unchanged from
the pinned Charon/Aeneas extraction. This file relates their finite scalar
state and exact Rust result to the previously proved `Resource.WorkMeter` model.

This is a theorem about the generated Lean bodies under the concrete imported
Aeneas runtime models and the explicitly supplied `Option::is_none_or` adapter.
Frontend correctness, the standard-library-model correspondence, Rust compiler
and machine semantics remain trust boundaries; whole-library coverage is not
claimed by these theorems.
-/

namespace BulksketchBridge.WorkMeter

open Aeneas Aeneas.Std

@[simp]
theorem toUInt64_toNat (word : U64) :
    (toUInt64 word).toNat = word.val := by rfl

/-- The scalar projection discards no generated-state bits. -/
theorem toUInt64_injective : Function.Injective toUInt64 := by
  intro left right h
  apply UScalar.eq_of_val_eq
  simpa only [toUInt64_toNat] using congrArg UInt64.toNat h

/-- Equality of projected states is equality of all generated state fields. -/
theorem toModel_injective : Function.Injective toModel := by
  intro left right h
  have hl := congrArg BulksketchProofs.Resource.WorkMeter.limit h
  have hu := congrArg BulksketchProofs.Resource.WorkMeter.used h
  have he := congrArg BulksketchProofs.Resource.WorkMeter.exhausted h
  have hl' : left.limit = right.limit := toUInt64_injective hl
  have hu' : left.used = right.used := toUInt64_injective hu
  have he' : left.exhausted = right.exhausted := he
  cases left
  cases right
  simp_all

/-- The concrete runtime's checked addition has exactly our finite-word meaning. -/
theorem checked_add_matches_model (left right : U64) :
    (U64.checked_add left right).map toUInt64 =
      BulksketchProofs.Resource.checkedAdd64 (toUInt64 left) (toUInt64 right) := by
  have hs := U64.checked_add_bv_spec left right
  cases hc : U64.checked_add left right with
  | none =>
    simp only [hc] at hs
    have hover : UInt64.size ≤ (toUInt64 left).toNat + (toUInt64 right).toNat := by
      simp only [toUInt64_toNat]
      have hm : U64.max = 18446744073709551615 := U64.max_eq
      rw [hm] at hs
      change 18446744073709551616 ≤ left.val + right.val
      omega
    have hm := (BulksketchProofs.Resource.checkedAdd64_none_iff
      (toUInt64 left) (toUInt64 right)).mpr hover
    simpa [hc] using hm.symm
  | some next =>
    simp only [hc] at hs
    have hsum : (toUInt64 left).toNat + (toUInt64 right).toNat < UInt64.size := by
      simp only [toUInt64_toNat]
      have hm : U64.max = 18446744073709551615 := U64.max_eq
      rw [hm] at hs
      change left.val + right.val < 18446744073709551616
      omega
    have hm := (BulksketchProofs.Resource.checkedAdd64_some_iff
      (toUInt64 left) (toUInt64 right) (toUInt64 next)).mpr
        ⟨hsum, by simpa only [toUInt64_toNat] using hs.2.1⟩
    simpa [hc] using hm.symm

/-- The actual generated constructor returns normally and establishes the model. -/
theorem new_refines (limit : U64) :
    ∃ final : GeneratedMeter,
      bulksketch.types.WorkMeter.new limit = Aeneas.Std.Result.ok final ∧
      toModel final = BulksketchProofs.Resource.WorkMeter.new (toUInt64 limit) := by
  refine ⟨{ limit, used := 0#u64, exhausted := false }, rfl, ?_⟩
  rfl

/-- Exact generated-body charge result and state; outer failure/panic is absent.

Both ordinary Rust return variants are retained: model success is Rust Ok(()),
and model denial is precisely Rust Err(WorkLimitExceeded), never another error.
No precondition excludes overflow, already-exhausted, or over-limit states.
-/
theorem charge_refines (meter : GeneratedMeter) (amount : U64) :
    ∃ final : GeneratedMeter,
      bulksketch.types.WorkMeter.charge meter amount =
        Aeneas.Std.Result.ok
          (rustOutcome ((toModel meter).charge (toUInt64 amount)).2, final) ∧
      toModel final = ((toModel meter).charge (toUInt64 amount)).1 := by
  cases he : meter.exhausted with
  | true =>
    have hm := (toModel meter).exhausted_sticky (toUInt64 amount) he
    rw [hm]
    refine ⟨meter, ?_, rfl⟩
    simp [bulksketch.types.WorkMeter.charge, Aeneas.Std.lift, he, rustOutcome]
  | false =>
    have hchecked := checked_add_matches_model meter.used amount
    cases hc : U64.checked_add meter.used amount with
    | none =>
      simp only [hc, Option.map_none] at hchecked
      have hm : (toModel meter).charge (toUInt64 amount) =
          ({ toModel meter with exhausted := true }, false) := by
        simp [BulksketchProofs.Resource.WorkMeter.charge, toModel, he, ← hchecked]
      rw [hm]
      refine ⟨{ meter with exhausted := true }, ?_, rfl⟩
      simp [bulksketch.types.WorkMeter.charge, Aeneas.Std.lift, hc, he,
        Aeneas.Std.core.option.Option.is_none_or, rustOutcome]
    | some next =>
      simp only [hc, Option.map_some] at hchecked
      by_cases hgt : meter.limit.val < next.val
      · have hm : (toModel meter).charge (toUInt64 amount) =
            ({ toModel meter with exhausted := true }, false) := by
          simpa [BulksketchProofs.Resource.WorkMeter.charge, toModel, he, ← hchecked] using hgt
        rw [hm]
        refine ⟨{ meter with exhausted := true }, ?_, rfl⟩
        simp [bulksketch.types.WorkMeter.charge, Aeneas.Std.lift, hc, he,
          Aeneas.Std.core.option.Option.is_none_or,
          bulksketch.types.WorkMeter.charge.closure.Insts.CoreOpsFunctionFnOnceTupleU64Bool.call_once,
          UScalar.lt_equiv, hgt, rustOutcome]
      · have hm : (toModel meter).charge (toUInt64 amount) =
            ({ toModel meter with used := toUInt64 next }, true) := by
          simpa [BulksketchProofs.Resource.WorkMeter.charge, toModel, he, ← hchecked]
            using (Nat.le_of_not_gt hgt)
        rw [hm]
        refine ⟨{ meter with used := next }, ?_, rfl⟩
        simp [bulksketch.types.WorkMeter.charge, Aeneas.Std.lift, hc, he,
          Aeneas.Std.core.option.Option.is_none_or,
          bulksketch.types.WorkMeter.charge.closure.Insts.CoreOpsFunctionFnOnceTupleU64Bool.call_once,
          Aeneas.Std.core.option.Option.expect, Aeneas.Std.Result.ofOption,
          UScalar.lt_equiv, hgt, rustOutcome]

end BulksketchBridge.WorkMeter
