import Arithmetic.Funs
import BulksketchProofs.Field.ReductionSpec

/-!
Frozen all-input contract for the original reduction called with the actual
source-generated Gf64 implementation dictionary. No arbitrary dictionary,
BITS premise, normal-return assumption, or precondition on the two words occurs.
The generic fallback remains in the unedited generated function.
-/
namespace BulksketchBridge.Gf64Reduce

open Aeneas.Std

def ReturnsFoldAndCertificate : Prop :=
  ∀ (product : bulksketch.types.RawProduct),
    ∃ output : U64,
      bulksketch.field.gf64.reduce
          bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField product = .ok output ∧
      output.bv = BulksketchProofs.Field.reduceFold64 product.lo.bv product.hi.bv ∧
      BulksketchProofs.Field.join128 product.lo.bv product.hi.bv =
        output.bv.setWidth 128 ^^^
          BulksketchProofs.Field.modulusMultiple128
            (product.hi.bv ^^^ BulksketchProofs.Field.overflow64 product.hi.bv)

end BulksketchBridge.Gf64Reduce
