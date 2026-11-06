import BulksketchBridge.Algebra.TraceSpec
import BulksketchProofs.Field.MapsSpec

/-! Fixed trace propositions: the target is Mathlib's linear algebra trace on
the exact degree-64 irreducible polynomial quotient. -/

namespace BulksketchBridge.Algebra.Gf64.TraceChallenges

def wordAbsoluteTraceIsAlgebraTrace : Prop :=
  ∀ input : BitVec 64,
    toField (BulksketchProofs.Field.Maps.absoluteTrace input) =
      algebraMap (ZMod 2) Field (Algebra.trace (ZMod 2) Field (toField input))

def nativeSelectorIsAlgebraTrace : Prop :=
  ∀ input : BitVec 64,
    Algebra.trace (ZMod 2) Field (toField input) =
      if BulksketchProofs.Field.Maps.traceBit input then 1 else 0

end BulksketchBridge.Algebra.Gf64.TraceChallenges
