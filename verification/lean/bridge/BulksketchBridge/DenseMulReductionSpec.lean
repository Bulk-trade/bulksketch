import Arithmetic.DenseMulReductionGenerated
import BulksketchBridge.Gf64ReduceSpec
import BulksketchBridge.PortableZipMap

namespace BulksketchBridge.DenseMulReductionSpec

open Aeneas Aeneas.Std BulksketchBridge.MutableZip
open bulksketch

scoped instance : Inhabited types.RawProduct := ⟨⟨0#u64, 0#u64⟩⟩

abbrev dictionary := field.Gf64.Insts.BulksketchFieldBinaryField

def reduceWord (product : types.RawProduct) : U64 :=
  ⟨BulksketchProofs.Field.reduceFold64 product.lo.bv product.hi.bv⟩

/-- The original final loop returns exhausted cursors and a backward callback.
Applying the callback reduces every remaining coefficient and preserves the
earlier destination entries and shared raw slice before the incoming callback.
The source method supplies equal length prefixes and the identity callback. -/
def finalReductionFrame : Prop :=
  ∀ {K : Type} (kernels : backend.contract.BulkKernels K field.Gf64),
    (∀ product, kernels.ArithmeticInst.reduce product = field.gf64.reduce dictionary product) →
    ∀ (dst : Slice U64) (raw : Slice types.RawProduct), dst.length = raw.length →
    ∀ start : Nat, start ≤ dst.length →
    ∀ back : State U64 types.RawProduct → State U64 types.RawProduct,
      ∃ restore : State U64 types.RawProduct → State U64 types.RawProduct,
        poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop1 dictionary kernels
          (stateAt dst raw start) back = Result.ok (stateAt dst raw dst.length, restore) ∧
        restore (stateAt dst raw dst.length) =
          back (stateAt (mapFrom dst raw (fun _ product => reduceWord product) start) raw dst.length)

end BulksketchBridge.DenseMulReductionSpec
