module
public import Aeneas
public import Workmeter.Types
@[expose] public section

/-!
Concrete executable model for the one standard-library operation missing from
Aeneas's unchanged WorkMeter extraction. No application body is replaced.

Native runtime source: Rust nightly-2026-09-17, core/src/option.rs:708-713.
`None` returns true; `Some x` invokes the supplied FnOnce on x. This runtime
model abstracts destructor/memory effects as the existing Aeneas FnOnce models do.
WorkMeter's captured comparison closure is a U64 value with no destructor effects.
The model's source correspondence is an explicit standard-library trust boundary;
it is not a proof of Rust's entire Option implementation or memory semantics.
The original generated FunsExternal_Template.lean remains untouched.
-/

namespace Aeneas.Std
open Result

@[rust_fun "core::option::{core::option::Option<@T>}::is_none_or"]
def core.option.Option.is_none_or
  {T F : Type _} (fnOnce : core.ops.function.FnOnce F T Bool)
  (value : Option T) (closure : F) : Result Bool :=
  match value with
  | none => ok true
  | some item => fnOnce.call_once closure item

end Aeneas.Std
