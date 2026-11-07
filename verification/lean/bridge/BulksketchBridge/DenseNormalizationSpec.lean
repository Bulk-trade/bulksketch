import Arithmetic.DenseNormalizationGenerated

namespace BulksketchBridge.DenseNormalization

open Aeneas.Std

/-- Length after discarding exactly the trailing zeros. The empty list and
an all-zero list both have normalized length zero. -/
def normalizedLength (coefficients : List U64) : Nat :=
  coefficients.length - (coefficients.reverse.takeWhile (· == 0#u64)).length

def NormalizedLenRefines : Prop :=
  ∀ coefficients : Slice U64, ∃ size : Usize,
    bulksketch.poly.dense.normalized_len coefficients = .ok size ∧
    size.val = normalizedLength coefficients.val

end BulksketchBridge.DenseNormalization
