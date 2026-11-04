import Aeneas
import BulksketchProofs.Field.ReductionSpec
import BulksketchProofs.Field.SpreadSpec

/-!
# Frozen full-word native GF64 square model

The specification reduces the exact 128-bit coefficient square assembled from
both halves of the input. It makes no assumption that the field modulus has
already been proved irreducible. The actual generated square body and concrete
Gf64 dictionary are named directly in the independent challenge propositions.
-/

namespace BulksketchBridge.Square

open Aeneas.Std

/-- Exact 64-bit remainder of the input's complete coefficient square. -/
def expectedWord (input : U64) : U64 :=
  ⟨BulksketchProofs.Field.reduceFold64
    (BulksketchProofs.Field.spread64 input.bv)
    (BulksketchProofs.Field.spread64 (input.bv >>> 32))⟩

end BulksketchBridge.Square
