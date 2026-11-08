import Arithmetic.Avx512RegisterGenerated
import BulksketchBridge.Algebra.WordSpec

namespace BulksketchBridge.Avx512RegisterChallenges

open Aeneas.Std Aeneas.Std.Avx512Register BulksketchProofs.Field
open BulksketchBridge.Algebra.Gf64 (multiplyWord)
open bulksketch.backend.x86_vpclmul512

def products (a b : Word512) (inputHigh : Bool) : Word512 :=
  fun pair outputHigh =>
    let product := clmul128 (a pair inputHigh) (b pair inputHigh)
    if outputHigh then (product >>> 64).setWidth 64 else product.setWidth 64

def shiftedReduction (low high : Word512) : Word512 :=
  fun pair half => reduceFold64 (low pair half) (high pair half)

def carrylessReduction (input : Word512) : Word512 :=
  fun pair high =>
    if high then input pair true ^^^ overflow64 (input pair true)
    else reduceFold64 (input pair false) (input pair true)

def productsReduced (a b : Word512) : Word512 :=
  fun pair half => multiplyWord (a pair half) (b pair half)

def rawRefines : Prop :=
  ∀ a b : Word512, raw a b = Result.ok (products a b false, products a b true)

def reduceShiftRefines : Prop :=
  ∀ low high : Word512, reduce_shift low high = Result.ok (shiftedReduction low high)

/-- Both words of each result pair are specified. The low half is the
field remainder and the high half carries the quotient. -/
def reduceClRefines : Prop :=
  ∀ input : Word512, reduce_cl input = Result.ok (carrylessReduction input)

def multiplyRefines : Prop :=
  ∀ (cl : Bool) (a b : Word512), multiply cl a b = Result.ok (productsReduced a b)

end BulksketchBridge.Avx512RegisterChallenges
