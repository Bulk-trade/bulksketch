module
public import Arithmetic.Types
public import Arithmetic.TrailingZeros
@[expose] public section

namespace Aeneas.Std

def Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    {T : Type u} {N : Usize} (array : Array T N) :
    Result (core.array.iter.IntoIter T N) :=
  .ok ⟨array.val⟩

def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
    {T : Type u} {N : Usize} (iter : core.array.iter.IntoIter T N) :
    Result (Option T × core.array.iter.IntoIter T N) :=
  match iter.remaining with
  | [] => .ok (none, iter)
  | head :: tail => .ok (some head, ⟨tail⟩)

end Aeneas.Std
