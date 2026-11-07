module
public import Aeneas
@[expose] public section

/-! Value models for the two external calls in the original normalization
extraction. The shared slice implementation of `rposition` in the pinned Rust
`core/src/slice/iter/macros.rs` consumes elements from the end, calls the
stateful predicate once per visited item and stops at the first match. Its
result index is relative to the remaining slice on entry. The returned
iterator retains the unvisited prefix and its original front cursor.

The Rust slice iterator's associated item is `&T`, represented by `T` in the
pinned Aeneas value model. The emitted external template separates the
associated item type parameters. The model uses their common Rust value type
and the concrete slice representation. Standard-library correspondence, drop
behavior and pointer/aliasing semantics remain within the documented runtime
trust boundary. -/

namespace Aeneas.Std

namespace ReversePosition

/-- Scan the remaining elements in reverse order, preserving callback failures
and threading the state returned by each preceding `FnMut` call. -/
def scan {T P : Type} (callback : core.ops.function.FnMut P T Bool) :
    List T → P → Result (Option Nat)
  | [], _ => .ok none
  | item :: rest, predicate => do
      let (matched, next) ← callback.call_mut predicate item
      if matched then .ok (some rest.length) else scan callback rest next

def retain {T : Type} (iterator : core.slice.iter.Iter T) (endIndex : Nat) :
    core.slice.iter.Iter T :=
  { iterator with
    slice := Slice.from (iterator.slice.val.take endIndex)
      ((List.length_take_le' _ _).trans iterator.slice.length_ineq) }

end ReversePosition

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::rposition"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.rposition
    {T P : Type} (callback : core.ops.function.FnMut P T Bool)
    (_exact : core.iter.traits.exact_size.ExactSizeIterator (core.slice.iter.Iter T) T)
    (_doubleEnded : core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.Iter T) T)
    (iterator : core.slice.iter.Iter T) (predicate : P) :
    Result (Option Usize × core.slice.iter.Iter T) := do
  let found ← ReversePosition.scan callback (iterator.slice.val.drop iterator.i).reverse predicate
  match found with
  | none => .ok (none, ReversePosition.retain iterator iterator.i)
  | some index => do
      let position ← UScalar.tryMk .Usize index
      .ok (some position, ReversePosition.retain iterator (iterator.i + index))

/-- None returns the supplied default. Some invokes the original FnOnce callback. -/
@[rust_fun "core::option::{core::option::Option<@T>}::map_or"]
def core.option.Option.map_or {T U F : Type _} (callback : core.ops.function.FnOnce F T U)
    (option : Option T) (fallback : U) (function : F) : Result U :=
  match option with
  | none => .ok fallback
  | some value => callback.call_once function value

end Aeneas.Std
