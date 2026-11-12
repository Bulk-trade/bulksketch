import BulksketchBridge.InverseSpec
import BulksketchBridge.Algebra.WordEquiv

/-! Independent quotient-field output specification for the original generic
inverse. The explicit callback contracts name the existing source arithmetic,
not a successful inverse call or an assumed inverse property. -/

namespace BulksketchBridge.Inverse

open Aeneas Aeneas.Std
open BulksketchBridge.Algebra.Gf64

/-- Callback word meanings discharged by the native multiplication and
unmodded native Frobenius refinement theorems. -/
def multiplyNativeWord (left right : U64) : U64 := ⟨multiplyWord left.bv right.bv⟩
def frobeniusNativeWord (input : U64) (count : U32) : U64 :=
  ⟨BulksketchProofs.Field.Period.iterateSquare count.val input.bv⟩

/-- Exactly None for zero; every other word has the unique represented field
inverse. The choice-free forward interpretation is the exact polynomial map;
its proved bijectivity supplies the inverse word. -/
noncomputable def expectedFieldInverse (input : U64) : Option U64 :=
  if input = 0#u64 then none else
    some ⟨wordFieldEquiv.symm (toField input.bv)⁻¹⟩

end BulksketchBridge.Inverse
