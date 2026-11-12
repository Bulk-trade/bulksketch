module
public import Aeneas
@[expose] public section

namespace Aeneas.Std.CertificateRuntime

/-- `Iterator::any` consumes elements until the first true predicate result.
The iterator and stateful predicate advance through their existing dictionaries. -/
def any {I F Item : Type} (iterator : core.iter.traits.iterator.Iterator I Item)
    (predicate : core.ops.function.FnMut F Item Bool) (initial : I) (callback : F) :
    Result (Bool × I) :=
  loop (fun (current, state) => do
    let (value, next) ← iterator.next current
    match value with
    | none => Result.ok (.done (false, next))
    | some item =>
      let (found, nextState) ← predicate.call_mut state item
      if found then Result.ok (.done (true, next))
      else Result.ok (.cont (next, nextState))) (initial, callback)

/-- The standard reference equality delegates to equality of the referents. -/
def mutableSharedEq {A B : Type} (equality : core.cmp.PartialEq A B)
    (left : A) (right : B) : Result Bool := equality.eq left right

end Aeneas.Std.CertificateRuntime
