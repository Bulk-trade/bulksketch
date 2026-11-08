import Arithmetic.DenseReducerSquareGenerated
import BulksketchBridge.DenseMulSpec
import BulksketchBridge.ClosedLeafAdvanceSpec
import BulksketchBridge.ClosedLeafWindows
import BulksketchBridge.SquareSpec

namespace BulksketchBridge.DenseReducerSquare

open Aeneas.Std DenseCoefficient RebuiltLfsr DenseNormalization
open DenseMulConvolutionSpec MutableZip
open DenseMulReductionSpec (reduceWord)
open bulksketch.backend.contract bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial
open scoped BulksketchBridge.DenseMulReductionSpec

abbrev Raw := bulksketch.types.RawProduct

def SquareAgrees {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ input, kernels.ArithmeticInst.square input = bulksketch.field.gf64.square dictionary input

def accumulateCoefficient (table : Slice U64) (degree index : Nat) (coefficient : U64)
    (raw : Slice Raw) : Slice Raw :=
  let square := Square.expectedWord coefficient
  let firstHigh := (degree + 1) / 2
  if index < firstHigh then
    raw.setAtNat (2 * index) { raw[2 * index]! with lo := raw[2 * index]!.lo ^^^ square }
  else
    let start := (index - firstHigh) * degree
    let row := ClosedLeaf.region table start (start + degree)
    mapFrom raw row (fun old entry => xorProduct old (RawMul.expectedProduct square entry)) 0

def accumulateSquare (a table : Slice U64) (degree : Nat) (raw : Slice Raw)
    (index : Nat) : Nat → Slice Raw
  | 0 => raw
  | count + 1 =>
    accumulateSquare a table degree (accumulateCoefficient table degree index a[index]! raw)
      (index + 1) count

def zeroRaw (raw : Slice Raw) (degree : Nat) : Slice Raw :=
  Slice.from (List.replicate (min degree raw.length) DenseMul.zeroProduct) (by
    simp only [List.length_replicate]
    exact (Nat.min_le_right _ _).trans raw.length_ineq)

def outputLength (out : Slice U64) (degree : Nat) : Usize :=
  ClosedLeafAdvance.usizeWord (normalizedLength (prefixSlice out degree).val)

def expectedOutput (a table dst active : Slice U64) (raw : Slice Raw)
    (degree : Nat) (accelerated : Bool) : Usize × Slice U64 × Slice Raw :=
  let dst1 := restorePrefix dst active
  if accelerated then (outputLength dst1 degree, dst1, raw)
  else
    let acc := accumulateSquare a table degree (zeroRaw raw degree) 0 a.length
    let reduced := mapFrom (prefixSlice dst1 degree) acc (fun _ product => reduceWord product) 0
    let out := restorePrefix dst1 reduced
    (outputLength out degree, out, raw.setSlice! 0 acc.val)

/-- The exact original source wrapper preserves both backend scratch paths,
including the scalar accumulation and final normalization. -/
def ActualSquareModInto : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (rawLaw : RawMulAgrees kernels) (squareLaw : SquareAgrees kernels) (reduceLaw : DenseMul.reduceAgrees kernels)
    (a modulus table dst : Slice U64) (raw : Slice Raw)
    (minModulus : 4 ≤ modulus.length) (monic : modulus[modulus.length - 1]! = 1#u64)
    (aRoom : a.length ≤ modulus.length - 1) (dstRoom : modulus.length - 1 ≤ dst.length)
    (rawRoom : 2 * (modulus.length - 1) < raw.length)
    (tableLen : table.length = (modulus.length - 1) * ((modulus.length - 1) / 2))
    (accelerated : Bool) (active : Slice U64) (returnedRaw : Slice Raw)
    (called : kernels.square_mod a table (prefixSlice dst (modulus.length - 1)) raw =
      .ok (accelerated, active, returnedRaw))
    (rawResultRoom : accelerated = false → modulus.length - 1 ≤ returnedRaw.length),
    square_mod_into dictionary kernels a modulus table dst raw =
      .ok (expectedOutput a table dst active returnedRaw (modulus.length - 1) accelerated)

end BulksketchBridge.DenseReducerSquare
