module
public import Aeneas
@[expose] public section

open Aeneas Aeneas.Std

/-- Models the pinned Rust core body with checked division, remainder, and increment. -/
@[rust_fun "core::num::{u64}::div_ceil"]
def core.num.U64.div_ceil (numerator denominator : U64) : Result U64 := do
  let quotient ← numerator / denominator
  let remainder ← numerator % denominator
  if remainder > 0#u64 then quotient + 1#u64 else Result.ok quotient
