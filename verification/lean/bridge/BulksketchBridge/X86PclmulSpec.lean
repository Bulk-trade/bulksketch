import Arithmetic.X86PclmulGenerated
import BulksketchBridge.RawMulSpec
import BulksketchBridge.SquareSpec
import BulksketchBridge.Algebra.WordSpec

namespace BulksketchBridge.X86Pclmul

open Aeneas.Std X86PclmulRuntime BulksketchProofs.Field
open bulksketch.backend.x86_pclmul
open bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic
open BulksketchBridge.Algebra.Gf64

abbrev dictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

def WordRefines : Prop :=
  ∀ input : U64, word input = Result.ok (input.bv.setWidth 128)

def LowRefines : Prop :=
  ∀ input : Xmm, low input = Result.ok (⟨input.setWidth 64⟩ : U64)

def WordsRefines : Prop :=
  ∀ input : Xmm, words input =
    Result.ok ({ lo := ⟨input.setWidth 64⟩, hi := ⟨(input >>> 64).setWidth 64⟩ } :
      bulksketch.types.RawProduct)

def RawProductRefines : Prop :=
  ∀ a b : U64, raw_product a b = Result.ok (RawMul.expectedProduct a b)

def RawMulRefines : Prop :=
  ∀ a b : U64, raw_mul dictionary a b = Result.ok (RawMul.expectedProduct a b)

/-- The carryless path retains its upper XOR word, while the fallback
zero-extends the reduced scalar. Both low words are canonical. -/
def ReducedRefines : Prop :=
  ∀ carryless : Bool, ∀ input : Xmm, reduced carryless dictionary input =
    Result.ok (join128 (reduceFold64 (input.setWidth 64) ((input >>> 64).setWidth 64))
      (if carryless then (input >>> 64).setWidth 64 ^^^ overflow64 ((input >>> 64).setWidth 64)
       else 0))

def MultiplyRefines : Prop :=
  ∀ carryless : Bool, ∀ a b : U64,
    multiply carryless dictionary a b = Result.ok (⟨multiplyWord a.bv b.bv⟩ : U64)

def MulRefines : Prop :=
  ∀ a b : U64, mul dictionary a b = Result.ok (⟨multiplyWord a.bv b.bv⟩ : U64)

def SquareRefines : Prop :=
  ∀ a : U64, square dictionary a = Result.ok (Square.expectedWord a)

end BulksketchBridge.X86Pclmul
