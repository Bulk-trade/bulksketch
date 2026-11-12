namespace BulksketchBridge.WorkspaceAdmission

/-- Lengths read from the nine workspace slices by the native admission check. -/
structure Lengths where
  syndromes : Nat
  bm : Nat
  polynomials : Nat
  factors : Nat
  squareTable : Nat
  verification : Nat
  roots : Nat
  raw : Nat
  stack : Nat
  deriving Repr, DecidableEq

/-- The extraction uses the x86_64 Darwin `usize` width. -/
abbrev usizeMax : Nat := 2 ^ 64 - 1

/-- The exact success condition with the checked arithmetic guards made explicit. -/
def Admitted (lengths : Lengths) (capacity budget : Nat) : Prop :=
  let width := budget + 1
  width ≤ usizeMax ∧
  (if budget = 0 then True else
    8 * width ≤ usizeMax ∧ width * width ≤ usizeMax ∧ 2 * (width * width) ≤ usizeMax ∧
    budget + 2 ≤ usizeMax ∧ 2 * (budget + 2) ≤ usizeMax) ∧
  2 * capacity ≤ usizeMax ∧ 2 * capacity + 1 ≤ usizeMax ∧
  capacity + 1 ≤ usizeMax ∧ 4 * (capacity + 1) ≤ usizeMax ∧
  budget * (budget / 2) ≤ usizeMax ∧
  2 * capacity + 1 ≤ lengths.syndromes ∧ 4 * (capacity + 1) ≤ lengths.bm ∧
  (if budget = 0 then 0 else 8 * width) ≤ lengths.polynomials ∧
  (if budget = 0 then 0 else 2 * (width * width)) ≤ lengths.factors ∧
  budget * (budget / 2) ≤ lengths.squareTable ∧ capacity ≤ lengths.verification ∧
  budget ≤ lengths.roots ∧ (if budget = 0 then 0 else 2 * (budget + 2)) ≤ lengths.raw ∧
  budget ≤ lengths.stack

instance (lengths : Lengths) (capacity budget : Nat) : Decidable (Admitted lengths capacity budget) := by
  unfold Admitted
  infer_instance

/-- `true` is Rust `Ok(())`, and `false` is `Err(ScratchTooSmall)`. -/
def check (lengths : Lengths) (capacity budget : Nat) : Bool := decide (Admitted lengths capacity budget)

end BulksketchBridge.WorkspaceAdmission
