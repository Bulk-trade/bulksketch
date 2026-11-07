import Arithmetic.PortableXorGenerated

namespace BulksketchBridge.PortableXorChallenges

open Aeneas.Std
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels

/-- Every valid word position in the destination is XORed with the corresponding
source word. The source assertion rejects unequal lengths before traversal. -/
def actualXorAssignReturnsFrame : Prop :=
  ∀ (F : Type) (field : bulksketch.field.BinaryField F) (dst src : Slice U64),
    (dst.length = src.length → ∃ output : Slice U64,
      xor_assign field dst src = Result.ok output ∧
      output.length = dst.length ∧
      ∀ i : Nat, i < dst.length → output[i]! = dst[i]! ^^^ src[i]!) ∧
    (dst.length ≠ src.length → xor_assign field dst src = Result.fail Error.panic)

end BulksketchBridge.PortableXorChallenges
