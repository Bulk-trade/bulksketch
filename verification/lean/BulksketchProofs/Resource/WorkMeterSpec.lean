import Init.Data.UInt.Basic

/-!
# Finite-width work-meter model definitions

This handwritten model follows `bulksketch/src/types.rs:272-301` at revision
`0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`. State and amounts are `UInt64`;
checked addition tests the exact sum against `UInt64.size` before accepting the
machine-word addition. Rust-source refinement is a separate unproved obligation.
-/

namespace BulksketchProofs.Resource

/-- The state represented by Rust's `limit`, `used`, and `exhausted` fields. -/
structure WorkMeter where
  limit : UInt64
  used : UInt64
  exhausted : Bool
  deriving DecidableEq, Repr

/-- Unsigned checked addition: no modular result escapes on overflow. -/
def checkedAdd64 (a b : UInt64) : Option UInt64 :=
  if a.toNat + b.toNat < UInt64.size then some (a + b) else none

/-- Constructor corresponding to `WorkMeter::new`. -/
def WorkMeter.new (limit : UInt64) : WorkMeter :=
  { limit, used := 0, exhausted := false }

/-- The final Boolean is true precisely for Rust's `Ok(())`. -/
def WorkMeter.charge (meter : WorkMeter) (amount : UInt64) : WorkMeter × Bool :=
  if meter.exhausted then
    ({ meter with exhausted := true }, false)
  else
    match checkedAdd64 meter.used amount with
    | none => ({ meter with exhausted := true }, false)
    | some next =>
      if next.toNat ≤ meter.limit.toNat then
        ({ meter with used := next }, true)
      else
        ({ meter with exhausted := true }, false)

/-- The meter invariant established by construction and preserved by charging. -/
def WorkMeter.Bounded (meter : WorkMeter) : Prop :=
  meter.used.toNat ≤ meter.limit.toNat

/-- Execute a sequence, stopping at the first denied charge. -/
def WorkMeter.chargeAll (meter : WorkMeter) : List UInt64 → WorkMeter × Bool
  | [] => (meter, true)
  | amount :: rest =>
      let step := meter.charge amount
      if step.2 then step.1.chargeAll rest else (step.1, false)

end BulksketchProofs.Resource
