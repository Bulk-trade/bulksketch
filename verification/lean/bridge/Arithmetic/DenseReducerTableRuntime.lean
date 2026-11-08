-- Value-level bindings for the original reducer's monic guard.
import Arithmetic.TimesXModGenerated

open Aeneas Aeneas.Std Result

namespace bulksketch.DenseReducerTableRuntime

/-- The shared slice's last word, if the slice is nonempty. -/
def last {T : Type} (words : Slice T) : Result (Option T) :=
  .ok words.val.getLast?

/-- Rust Option equality compares variants, using the provided equality
dictionary only when both options contain an element. -/
def optionEq {T : Type} (cmp : core.cmp.PartialEq T T)
    (left right : Option T) : Result Bool :=
  match left, right with
  | none, none => .ok true
  | some a, some b => cmp.eq a b
  | _, _ => .ok false

end bulksketch.DenseReducerTableRuntime
