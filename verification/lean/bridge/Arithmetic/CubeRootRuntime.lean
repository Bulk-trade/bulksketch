module
public import Aeneas
@[expose] public section

namespace Aeneas.Std.CubeRootRuntime

/-- Value model of pinned Rust `bool::then_some`. The source evaluates the
argument before the call. Both result branches preserve its exact value. -/
def thenSome {T : Type} (condition : Bool) (value : T) : Result (Option T) :=
  Result.ok (if condition then some value else none)

end Aeneas.Std.CubeRootRuntime
