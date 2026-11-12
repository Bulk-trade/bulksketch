import BulksketchBridge.DenseMulConvolutionSpec
import BulksketchBridge.DenseNormalizationSpec

namespace BulksketchBridge.DenseMul

open Aeneas.Std DenseMulConvolutionSpec MutableZip
open DenseMulReductionSpec (reduceWord)
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial

abbrev Raw := bulksketch.types.RawProduct

def takeSlice {T : Type} (buffer : Slice T) (length : Nat) : Slice T :=
  Slice.from (buffer.val.take length) (by
    rw [List.length_take]
    exact (Nat.min_le_right _ _).trans buffer.length_ineq)

def zeroProduct : Raw := ⟨0#u64, 0#u64⟩

def clearedRaw (raw : Slice Raw) (length : Nat) : Slice Raw :=
  raw.setSlice! 0 (List.replicate length zeroProduct)

def finishedRaw (a b : Slice U64) (raw : Slice Raw) : Slice Raw :=
  accumulateRows a b (clearedRaw raw (a.length + b.length - 1)) 0 a.length

open scoped BulksketchBridge.DenseMulReductionSpec in
def finishedDst (a b dst : Slice U64) (raw : Slice Raw) : Slice U64 :=
  let length := a.length + b.length - 1
  dst.setSlice! 0 (mapFrom (takeSlice dst length) (takeSlice (finishedRaw a b raw) length)
    (fun _ product => reduceWord product) 0).val

def reduceAgrees {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ product, kernels.ArithmeticInst.reduce product = bulksketch.field.gf64.reduce dictionary product

/-- Exact scratch frames and normalized length, with errors interpreted by the
checked scalar and assertion behavior of the generated model. -/
def ActualDenseMulReturnsExactFrames : Prop :=
  ∀ {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64),
    RawMulAgrees kernels → reduceAgrees kernels →
    ∀ (a b dst : Slice U64) (raw : Slice Raw),
      if a.length = 0 ∨ b.length = 0 then
        mul_into dictionary kernels a b dst raw = Result.ok (0#usize, dst, raw)
      else if a.length + b.length ≤ Usize.max then
        if a.length + b.length ≤ dst.length ∧ a.length + b.length ≤ raw.length then
          ∃ normalized : Usize,
            mul_into dictionary kernels a b dst raw =
              Result.ok (normalized, finishedDst a b dst raw, finishedRaw a b raw) ∧
            normalized.val =
              DenseNormalization.normalizedLength
                ((finishedDst a b dst raw).val.take (a.length + b.length - 1))
        else mul_into dictionary kernels a b dst raw = Result.fail Error.assertionFailure
      else mul_into dictionary kernels a b dst raw = Result.fail Error.integerOverflow

end BulksketchBridge.DenseMul
