import Arithmetic.Funs
import BulksketchProofs.Field.ReductionSpec

/-!
Frozen contract for the original generic reduction's GF64 branch. The sole
dictionary hypothesis is a successful BITS=64 result. The fallback body is
retained unchanged; its general-field correctness is a separate open contract.
No hypothesis assumes that reduction already returns normally.
-/

namespace BulksketchBridge.Reduce

open Aeneas.Std

def RefinesGF64 : Prop :=
  ∀ {F : Type} (dictionary : bulksketch.field.BinaryField F)
    (product : bulksketch.types.RawProduct),
    dictionary.BITS = .ok 64#u32 →
    ∃ output : U64,
      bulksketch.field.gf64.reduce dictionary product = .ok output ∧
      output.bv = BulksketchProofs.Field.reduceFold64 product.lo.bv product.hi.bv

def DivisionCertificateGF64 : Prop :=
  ∀ {F : Type} (dictionary : bulksketch.field.BinaryField F)
    (product : bulksketch.types.RawProduct),
    dictionary.BITS = .ok 64#u32 →
    ∃ output : U64,
      bulksketch.field.gf64.reduce dictionary product = .ok output ∧
      BulksketchProofs.Field.join128 product.lo.bv product.hi.bv =
        output.bv.setWidth 128 ^^^
          BulksketchProofs.Field.modulusMultiple128
            (product.hi.bv ^^^ BulksketchProofs.Field.overflow64 product.hi.bv)

end BulksketchBridge.Reduce
