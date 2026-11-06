import Arithmetic.PortableInverseGenerated
import BulksketchBridge.InverseFieldSpec

namespace BulksketchBridge.PortableInverseChallenges

open Aeneas.Std

/-- Every original Portable inverse call returns None exactly for zero and
otherwise the unique word representing the actual Mathlib field inverse. -/
def actualInverseReturnsFieldInverse : Prop :=
  ∀ input : U64,
    bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.inverse
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input =
        Result.ok (Inverse.expectedFieldInverse input)

end BulksketchBridge.PortableInverseChallenges
