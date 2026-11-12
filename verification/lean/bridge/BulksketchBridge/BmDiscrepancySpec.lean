import Arithmetic.BmLocatorGenerated
import BulksketchBridge.RawMulSpec
import BulksketchBridge.Algebra.WordSpec
import BulksketchBridge.ClosedLeafWindows

namespace BulksketchBridge.BmDiscrepancy

open Aeneas.Std Algebra.Gf64 bulksketch.backend.contract bulksketch.decode.bm
open BulksketchProofs.Field
open scoped BigOperators

abbrev Raw := bulksketch.types.RawProduct
abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
abbrev Forward := core.slice.iter.Iter U64
abbrev Reverse := core.iter.adapters.rev.Rev Forward
abbrev DiscrepancyZip := core.iter.adapters.zip.Zip Forward Reverse

def RawArithmetic {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ left right, kernels.ArithmeticInst.raw_mul left right =
    bulksketch.field.gf64.raw_mul fieldDictionary left right

def ReduceArithmetic {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ product, kernels.ArithmeticInst.reduce product = bulksketch.field.gf64.reduce fieldDictionary product

def rawXor (left right : Raw) : Raw :=
  { lo := left.lo ^^^ right.lo, hi := left.hi ^^^ right.hi }

def rawFold (pairs : List (U64 × U64)) (initial : Raw) : Raw :=
  pairs.foldl (fun acc pair => rawXor acc (RawMul.expectedProduct pair.1 pair.2)) initial

noncomputable def rawValue (product : Raw) : Field :=
  toField (reduceFold64 product.lo.bv product.hi.bv)

def remainingPairs (coefficients syndromes : Slice U64) (index : Nat) : List (U64 × U64) :=
  (coefficients.val.drop index).zip syndromes.val.reverse

/-- A forward coefficient cursor and the remaining reverse syndrome slice.
The shared backwards iterator leaves its initial zero front cursor intact. -/
def zipAt (coefficients syndromes : Slice U64) (index : Nat) : DiscrepancyZip :=
  ⟨⟨coefficients, index⟩, ⟨⟨syndromes, 0⟩⟩⟩

def sourceZip (connection syndromes : Slice U64) (degree step : Nat) : DiscrepancyZip :=
  zipAt (DenseCoefficient.prefixSlice connection (degree + 1))
    (ClosedLeaf.region syndromes (step + 1 - degree) (step + 2)) 0

/-- Both source-instantiation branches return exactly the two complete
carryless XOR halves for the same forward/reverse zip. -/
def ActualBmRawDiscrepancy : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64), RawArithmetic kernels →
    ∀ (coefficients syndromes : Slice U64) (index : Nat) (initial : Raw),
      let state := zipAt coefficients syndromes index
      let result := rawFold (remainingPairs coefficients syndromes index) initial
      locator_loop0_loop1 fieldDictionary kernels state initial.lo initial.hi = .ok (result.lo, result.hi) ∧
      locator_loop0_loop6 fieldDictionary kernels state initial.lo initial.hi = .ok (result.lo, result.hi)

/-- The original read-only loop and the caller's single reduction compute
the discrepancy with ascending coefficients and descending syndromes.
The windows start at the source ranges admitted by the BM invariant. -/
def ActualBmSourceDiscrepancy : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    RawArithmetic kernels → ReduceArithmetic kernels →
    ∀ (connection syndromes : Slice U64) (degree step : Nat),
      degree < connection.length → degree ≤ step + 1 → step + 1 < syndromes.length →
      let state := sourceZip connection syndromes degree step
      ∃ delta : U64,
        (do
          let (lo, hi) ← locator_loop0_loop1 fieldDictionary kernels state 0#u64 0#u64
          kernels.ArithmeticInst.reduce ⟨lo, hi⟩) = .ok delta ∧
        (do
          let (lo, hi) ← locator_loop0_loop6 fieldDictionary kernels state 0#u64 0#u64
          kernels.ArithmeticInst.reduce ⟨lo, hi⟩) = .ok delta ∧
        toField delta.bv = ∑ i ∈ Finset.range (degree + 1),
          toField connection[i]!.bv * toField syndromes[step + 1 - i]!.bv

end BulksketchBridge.BmDiscrepancy
