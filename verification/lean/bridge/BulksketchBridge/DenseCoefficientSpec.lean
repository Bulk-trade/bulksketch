import Arithmetic.DenseCoefficientGenerated
import BulksketchBridge.DenseCoefficientState
import BulksketchBridge.DenseNormalizationSpec

namespace BulksketchBridge.DenseCoefficient

open Aeneas Aeneas.Std

/-- The original method returns the normalized active length and the entire
fixed-size buffer on valid inputs. Either invalid guard is an assertion
failure. The field and backend dictionaries are arbitrary. -/
def XorCoefficientRefines : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F)
    (backend : bulksketch.backend.contract.BulkKernels K F)
    (original : Slice U64) (length index : Usize) (value : U64),
    let source := bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.xor_coefficient
      field backend original length index value
    if length.val ≤ original.length ∧ index.val < original.length then
      ∃ normalized : Usize, ∃ result : Slice U64,
        source = .ok (normalized, result) ∧
        result.length = original.length ∧
        (∀ slot, slot < original.length →
          result[slot]! = expectedCoefficient original length.val index.val value slot) ∧
        normalized.val = DenseNormalization.normalizedLength
          (result.val.take (activeSize length.val index.val))
    else source = .fail .assertionFailure

end BulksketchBridge.DenseCoefficient
