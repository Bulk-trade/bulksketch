import Arithmetic.InverseGenerated

/-! Exact operational contracts for the original generic inversion routine.
Callback behavior is stated explicitly and universally; normal return of the
inversion routine itself is a conclusion. The caller must separately discharge
these callback contracts from the selected arithmetic implementation. -/

namespace BulksketchBridge.Inverse

open Aeneas Aeneas.Std

abbrev Iterator := core.iter.adapters.rev.Rev (core.ops.range.Range U32)

def iteratorAt (remaining : Nat) : Iterator :=
  { iter := { start := 0#u32, «end» := ⟨BitVec.ofNat 32 remaining⟩ } }

def chainIndex (count : Nat) : U32 := ⟨BitVec.ofNat 32 (2 ^ (count + 1) - 1)⟩

def chain (multiply : U64 → U64 → U64) (frobenius : U64 → U32 → U64)
    (input : U64) : Nat → U64
  | 0 => input
  | count + 1 => multiply
      (frobenius (multiply (frobenius (chain multiply frobenius input count)
        (chainIndex count)) (chain multiply frobenius input count)) (1#u32)) input

def expectedResult (multiply : U64 → U64 → U64) (frobenius : U64 → U32 → U64)
    (input : U64) : Option U64 :=
  if input = 0#u64 then none else
  if input = 1#u64 then some (1#u64) else
  some (frobenius (chain multiply frobenius input 5) (1#u32))

def MulNormal {T : Type} (dictionary : core.ops.function.Fn T (U64 × U64) U64)
    (callback : T) (multiply : U64 → U64 → U64) : Prop :=
  ∀ left right, dictionary.call callback (left, right) = Result.ok (multiply left right)

def FrobeniusNormal {T : Type} (dictionary : core.ops.function.Fn T (U64 × U32) U64)
    (callback : T) (frobenius : U64 → U32 → U64) : Prop :=
  ∀ input count, dictionary.call callback (input, count) = Result.ok (frobenius input count)

end BulksketchBridge.Inverse
