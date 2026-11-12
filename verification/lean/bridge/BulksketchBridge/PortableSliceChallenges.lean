import Arithmetic.PortableSliceGenerated
import BulksketchBridge.PortableZipMap
import BulksketchBridge.SquareSpec
import BulksketchBridge.Algebra.WordSpec

namespace BulksketchBridge.PortableSliceChallenges

open Aeneas.Std BulksketchBridge.MutableZip BulksketchBridge.Algebra.Gf64
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic

def squareRefines : Prop :=
  ∀ dst src : Slice U64,
    square_slice bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField dst src =
      if dst.length = src.length then Result.ok (mapFrom dst src (fun _ word => Square.expectedWord word) 0)
      else Result.fail .panic

def scaleValue (scale left right : U64) : U64 :=
  left ^^^ (⟨multiplyWord right.bv scale.bv⟩ : U64)

def scaleRefines : Prop :=
  ∀ (dst src : Slice U64) (scale : U64),
    scale_xor bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField dst src scale =
      if dst.length = src.length then Result.ok (mapFrom dst src (scaleValue scale) 0)
      else Result.fail .panic

end BulksketchBridge.PortableSliceChallenges
