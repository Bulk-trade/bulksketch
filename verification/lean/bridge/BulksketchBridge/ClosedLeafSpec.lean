import Arithmetic.ClosedLeafGenerated
import BulksketchBridge.ClosedLeafWindows
import BulksketchBridge.StageChargeSpec
import BulksketchBridge.CertificateSpec
import BulksketchBridge.CubicSpec

namespace BulksketchBridge.ClosedLeaf

open Aeneas.Std DenseCoefficient
open bulksketch.types bulksketch.decode.roots bulksketch.decode.scratch bulksketch.backend.contract

abbrev LeafReply := core.result.Result (core.result.Result Stage DecodeFailure) DecodeError
abbrev LeafReturn := LeafReply × Roots × RowWorkspace × (RowWorkspace → RowWorkspace) × WorkMeter
abbrev fieldDictionary := Cubic.fieldDictionary

def verifying : Stage → Bool
  | .FactorVerification => true
  | _ => false

def leafOperation (roots : Roots) (stage : Stage) : bulksketch.decode.work.Charge :=
  if verifying stage then .FactorVerification roots.degree
  else if roots.degree = 3#usize then .LeafThree else .LeafFour

def leafPrice (roots : Roots) (stage : Stage) : U64 :=
  if verifying stage then
    if roots.degree = 3#usize then 31#u64 else 49#u64
  else if roots.degree = 3#usize then 640#u64 else 2048#u64

def factorWords (roots : Roots) (workspace : RowWorkspace) : Slice U64 :=
  prefixSlice workspace.polynomials (roots.degree.val + 1)

def candidateWords (roots : Roots) (workspace : RowWorkspace) : Slice U64 :=
  region workspace.polynomials 11 (11 + roots.solved_count.val)

def productWords (workspace : RowWorkspace) : Slice U64 :=
  region workspace.polynomials 15 20

def certificateResult (roots : Roots) (workspace : RowWorkspace) : Bool × Slice U64 :=
  Certificate.expected (factorWords roots workspace) (candidateWords roots workspace) (productWords workspace)

def checkedWorkspace (workspace : RowWorkspace) (product : Slice U64) : RowWorkspace :=
  { workspace with polynomials := workspace.polynomials.setSlice! 15 product.val }

def acceptedWorkspace (roots : Roots) (workspace : RowWorkspace) (product : Slice U64) : RowWorkspace :=
  { checkedWorkspace workspace product with
    roots := workspace.roots.setSlice! roots.count.val (candidateWords roots workspace).val }

structure Admitted (roots : Roots) (stage : Stage) (workspace : RowWorkspace) : Prop where
  degree : roots.degree = 3#usize ∨ roots.degree = 4#usize
  candidateRoom : 15 ≤ workspace.polynomials.length
  verificationRoom : verifying stage = true → 20 ≤ workspace.polynomials.length
  candidateCount : verifying stage = true → roots.solved_count.val ≤ 4
  rootRoom : verifying stage = true → (certificateResult roots workspace).1 = true →
    roots.count.val + roots.degree.val ≤ workspace.roots.length

def normalReturn (stage : Stage) (roots : Roots) (workspace : RowWorkspace)
    (meter : WorkMeter) : LeafReturn :=
  (.Ok (.Ok stage), roots, workspace, id, meter)

/-- Exact state after the selected native solver returns. -/
def solveFrame (roots : Roots) (workspace : RowWorkspace) (meter : WorkMeter)
    (result : Option Usize × Slice U64) : LeafReturn :=
  let updated := { workspace with polynomials := workspace.polynomials.setSlice! 11 result.2.val }
  match result.1 with
  | none => normalReturn .ReducerPreparation roots updated meter
  | some count => normalReturn .FactorVerification { roots with solved_count := count } updated meter

def verificationFrame (roots : Roots) (workspace : RowWorkspace) (meter : WorkMeter) : Result LeafReturn :=
  let (valid, product) := certificateResult roots workspace
  if valid then do
    let count ← roots.count + roots.degree
    let (next, updated, final, back) ← Roots.advance { roots with count } (acceptedWorkspace roots workspace product)
    .ok (.Ok (.Ok next), updated, final, back, meter)
  else .ok (normalReturn .ReducerPreparation roots (checkedWorkspace workspace product) meter)

/-- Exact source phase equation. The selected solver and stack advance
are the actual generated bodies, each checked independently. -/
def expected {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (stage : Stage) (workspace : RowWorkspace) (meter : WorkMeter) : Result LeafReturn := do
  let (charge, finalMeter) := StageCharge.chargeResult meter (.Ok (leafPrice roots stage))
  match charge with
  | .Err error => .ok (.Err error, roots, workspace, id, finalMeter)
  | .Ok () =>
    if verifying stage then verificationFrame roots workspace finalMeter
    else
      let result ← bulksketch.decode.deg34.solve fieldDictionary kernels (factorWords roots workspace)
        (region workspace.polynomials 11 15)
      .ok (solveFrame roots workspace finalMeter result)

def ActualClosedLeafRefines : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (stage : Stage) (workspace : RowWorkspace) (meter : WorkMeter),
    Cubic.CorrectArithmetic kernels → Admitted roots stage workspace →
    Roots.closed_leaf fieldDictionary kernels roots stage workspace meter =
      expected kernels roots stage workspace meter

end BulksketchBridge.ClosedLeaf
