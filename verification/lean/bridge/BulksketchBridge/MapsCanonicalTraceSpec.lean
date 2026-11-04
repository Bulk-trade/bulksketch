import Aeneas
import BulksketchProofs.Field.MapsSpec

/-!
Exact complete-byte specification for the original canonical trace fallback.
The output is the complete sum of all 64 polynomial conjugates, represented
by the independently defined absolute-trace model. No successful source return,
trace-bit bound, canonical-input assumption, or field-irreducibility hypothesis
is a premise of the source challenge.
-/

namespace BulksketchBridge.MapsCanonicalTrace

open Aeneas.Std

def expectedWord (input : U64) : U8 :=
  ⟨(BulksketchProofs.Field.Maps.absoluteTrace input.bv).setWidth 8⟩

end BulksketchBridge.MapsCanonicalTrace
