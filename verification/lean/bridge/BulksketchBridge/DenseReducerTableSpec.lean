import Arithmetic.DenseReducerTableGenerated
import BulksketchBridge.TimesXModSpec
import BulksketchBridge.DenseCoefficientPolynomial

namespace BulksketchBridge.DenseReducerTable

open Aeneas.Std Algebra.Gf64 DenseCoefficient TimesXMod
open bulksketch.backend.contract

abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

/-- The actual fixed-width update shifts the original words, then adds
the outgoing word times the original low modulus prefix. -/
def stepWords (modulus current : Slice U64) : Slice U64 :=
  let shifted := shiftedWords current
  let low := prefixSlice modulus current.length
  let scale := current[current.length - 1]!
  Slice.from (List.ofFn fun index : Fin current.length =>
    shifted[index.val]! ^^^ (⟨multiplyWord scale.bv low[index.val]!.bv⟩ : U64))
    (by simp only [List.length_ofFn]; exact current.length_ineq)

def initialWords (modulus : Slice U64) (degree : Nat) : Slice U64 :=
  let low := prefixSlice modulus degree
  if degree % 2 = 0 then low else stepWords modulus low

/-- Write a full row before making the two modular shifts for the next row.
The final row returns its current words without an additional shift. -/
def fillRows (modulus : Slice U64) (degree : Nat) (table current : Slice U64)
    (row : Nat) : Nat → Slice U64 × Slice U64
  | 0 => (table, current)
  | count + 1 =>
    fillRows modulus degree (table.setSlice! (row * degree) current.val)
      (if count = 0 then current else stepWords modulus (stepWords modulus current))
      (row + 1) count

def expectedTable (modulus table work : Slice U64) : Slice U64 × Slice U64 :=
  let degree := modulus.length - 1
  let result := fillRows modulus degree table (initialWords modulus degree) 0 (degree / 2)
  (result.1, work.setSlice! 0 result.2.val)

/-- Original native table construction with exact table and work writeback. -/
def ActualPrepareSquareTable : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    ExactScaleXor kernels →
    ∀ (modulus table work : Slice U64),
      4 ≤ modulus.length → modulus[modulus.length - 1]! = 1#u64 →
      (modulus.length - 1) * ((modulus.length - 1) / 2) ≤ table.length →
      4 * modulus.length ≤ work.length →
      bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.prepare_square_table
        fieldDictionary kernels modulus table work = .ok (expectedTable modulus table work)

end BulksketchBridge.DenseReducerTable
