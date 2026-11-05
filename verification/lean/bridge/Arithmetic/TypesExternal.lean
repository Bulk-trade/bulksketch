module
public import Aeneas
@[expose] public section

/-!
Concrete value model of the remaining owned elements of Rust's array iterator.
The standard-library correspondence, ownership/drop behavior and representation
are explicit trusted boundaries, not application axioms or proved Rust code.
-/

namespace Aeneas.Std

structure core.array.iter.IntoIter (T : Type u) (_N : Usize) where
  remaining : List T

end Aeneas.Std
