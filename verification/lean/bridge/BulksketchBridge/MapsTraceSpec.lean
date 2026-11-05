import Aeneas

/-!
Frozen complete-word specification for the native Gf64 trace selector.
This exact source-behavior contract does not yet identify the bit selector with
the mathematical absolute trace. That separate semantic theorem uses independent
polynomial-square/period and basis certificates.
-/

namespace BulksketchBridge.MapsTrace

open Aeneas.Std

/-- The native selector, including every zero high output bit. -/
def expectedBits (input : BitVec 64) : BitVec 8 :=
  (((input >>> 61) ^^^ (input >>> 63)) &&& 1).setWidth 8

def expectedWord (input : U64) : U8 := ⟨expectedBits input.bv⟩

end BulksketchBridge.MapsTrace
