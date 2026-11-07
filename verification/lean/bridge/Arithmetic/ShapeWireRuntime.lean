module
public import Aeneas
@[expose] public section

namespace bulksketch

open Aeneas.Std

/-- Rust's `Option<T>` implementation of `Try::branch`. -/
def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type}
    (value : Option T) : Result (core.ops.control_flow.ControlFlow (Option Never) T) :=
  Result.ok (match value with
    | some value => .Continue value
    | none => .Break none)

/-- The `None` residual has no inhabited `Some` alternative. -/
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
    (T : Type) (value : Option Never) : Result (Option T) :=
  match value with
  | none => Result.ok none
  | some impossible => nomatch impossible

/-- Convert Rust's value-level `Result` to the corresponding `Option`. -/
def core.result.Result.ok {T E : Type} (value : Aeneas.Std.core.result.Result T E) :
    Aeneas.Std.Result (Option T) :=
  Aeneas.Std.Result.ok (match value with
    | .Ok value => some value
    | .Err _ => none)

end bulksketch
