import Aeneas
import BulksketchProofs.Field.MapsSpec

/-!
Frozen independent source-meaning targets for the native GF64 quadratic map.
The pure core tables and matrix/chunk maps are independent of the generated
application control flow. All public input words are admitted, including those
with trace one. The solver returns None for trace one and its fixed-bit-zero
matrix solution otherwise; successful source return is never assumed.
-/

namespace BulksketchBridge.MapsQuadratic

open Aeneas.Std

/-- Complete native table-lookup output before the matrix equality is applied. -/
def expectedChunkWord (input : U64) : U64 :=
  ⟨BulksketchProofs.Field.Maps.quadraticChunkValue input.bv⟩

def expectedMatrixWord (input : U64) : U64 :=
  ⟨BulksketchProofs.Field.Maps.quadraticValue input.bv⟩

def expectedSolution (input : U64) : Option U64 :=
  if BulksketchProofs.Field.Maps.traceBit input.bv then none
  else some (expectedMatrixWord input)

end BulksketchBridge.MapsQuadratic
