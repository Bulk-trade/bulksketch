import Arithmetic.PortableInsertionGenerated
import Arithmetic.PortableEncodingGenerated
import BulksketchBridge.Algebra.WordSpec
import BulksketchBridge.SquareSpec

namespace BulksketchBridge.PortableEncoding

open Aeneas.Std BulksketchBridge.Algebra.Gf64

def wordMul (left right : U64) : U64 := ⟨multiplyWord left.bv right.bv⟩

def powerFrom (square initial : U64) : Nat → U64
  | 0 => initial
  | n + 1 => wordMul (powerFrom square initial n) square

/-- The first stored syndrome has exponent one, then each step adds two. -/
def oddPower (id : U64) (slot : Nat) : U64 := powerFrom (Square.expectedWord id) id slot

def foldColumn (ids : List U64) (slot : Nat) (initial : U64) : U64 :=
  ids.foldl (fun value id => value ^^^ oddPower id slot) initial

end BulksketchBridge.PortableEncoding

namespace BulksketchBridge.PortableEncodingChallenges

open Aeneas.Std PortableEncoding
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels

def actualInsertNonzeroReturnsFrame : Prop :=
  ∀ odd ids : Slice U64, ∃ output : Slice U64,
    insert_nonzero bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField odd ids = Result.ok output ∧
    output.length = odd.length ∧
    ∀ slot, slot < odd.length → output[slot]! = foldColumn ids.val slot odd[slot]!

def actualEncodeNonzeroReturnsFrame : Prop :=
  ∀ (Backend : Type) (kernels : bulksketch.backend.contract.BulkKernels Backend bulksketch.field.Gf64),
    (∀ odd ids, kernels.insert_nonzero odd ids =
      insert_nonzero bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField odd ids) →
    ∀ odd ids : Slice U64, ∃ output : Slice U64,
      bulksketch.backend.contract.BulkKernels.encode_nonzero.default kernels odd ids = Result.ok output ∧
      output.length = odd.length ∧
      ∀ slot, slot < odd.length → output[slot]! = foldColumn ids.val slot 0#u64

end BulksketchBridge.PortableEncodingChallenges
