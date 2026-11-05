import Aeneas
import BulksketchProofs.Field.SpreadSpec

/-!
# Frozen full-word correspondence for the actual generated spread body

This definition preserves all 64 scalar bits. Its specification is the existing
kernel-checked native-shaped bitvector model. Charon/Aeneas translation, the
standard scalar semantics and the Rust compiler/machine remain explicit trust
boundaries; this does not replace or modify the generated application body.
-/

namespace BulksketchBridge.Spread

open Aeneas.Std

/-- The complete expected generated scalar, with no discarded output bits. -/
def expectedWord (input : U64) : U64 :=
  ⟨BulksketchProofs.Field.spread64 input.bv⟩

end BulksketchBridge.Spread
