import Arithmetic.RootLeafGenerated
import BulksketchBridge.DirectTwoSpec
import BulksketchBridge.ClosedLeafAdvanceSpec

namespace BulksketchBridge.RootLeaf

open Aeneas.Std bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open bulksketch.backend.contract

abbrev LeafReply := core.result.Result (core.result.Result Stage DecodeFailure) DecodeError
abbrev LeafFrame := LeafReply × Roots × RowWorkspace × (RowWorkspace → RowWorkspace) × WorkMeter

def emptyRoots : Slice U64 := Slice.from [] (by simp)
def oneRoot (root : U64) : Slice U64 := Slice.from [root] (by change 1 ≤ Usize.max; scalar_tac)
def twoRoots (first second : U64) : Slice U64 := (Array.make 2#usize [first, second]).to_slice

noncomputable def quadraticTarget (constant linear : U64) : U64 :=
  Inverse.multiplyNativeWord constant (Square.expectedWord (DirectTwo.inverseWord linear))

noncomputable def leafCandidates (degree : Nat) (polynomials : Slice U64) :
    core.result.Result (Slice U64) DecodeFailure :=
  match degree with
  | 0 => .Ok emptyRoots
  | 1 => .Ok (oneRoot polynomials[0]!)
  | _ =>
    let linear := polynomials[1]!
    if linear = 0#u64 then .Err .NotSplit else
      match MapsQuadratic.expectedSolution (quadraticTarget polynomials[0]! linear) with
      | none => .Err .NotSplit
      | some solution =>
        let root := Inverse.multiplyNativeWord linear solution
        .Ok (twoRoots root (root ^^^ linear))

def LeafBounds (roots : Roots) (workspace : RowWorkspace) : Prop :=
  roots.degree.val ≤ 2 ∧
  roots.degree.val ≤ workspace.polynomials.length ∧
  roots.count.val + roots.degree.val ≤ workspace.roots.length

def leafResume (roots : Roots) (workspace : RowWorkspace) (words : Slice U64) (meter : WorkMeter) :
    Result LeafFrame := do
  let updatedRoots := { roots with count := ClosedLeafAdvance.usizeWord (roots.count.val + roots.degree.val) }
  let updatedWorkspace := { workspace with roots := workspace.roots.setSlice! roots.count.val words.val }
  let (stage, state, final, back) ← Roots.advance updatedRoots updatedWorkspace
  .ok (.Ok (.Ok stage), state, final, back, meter)

noncomputable def expectedLeaf (roots : Roots) (workspace : RowWorkspace) (meter : WorkMeter) :
    Result LeafFrame := do
  let price ← bulksketch.decode.work.WorkScheduleV1.cost (.Leaf roots.degree)
  let (paid, meter') := StageCharge.chargeResult meter price
  match paid with
  | .Err reason => .ok (.Err reason, roots, workspace, id, meter')
  | .Ok () =>
    match leafCandidates roots.degree.val workspace.polynomials with
    | .Err reason => .ok (.Ok (.Err reason), roots, workspace, id, meter')
    | .Ok words =>
      if 0#u64 ∈ words.val then .ok (.Ok (.Err .InvalidLocator), roots, workspace, id, meter')
      else leafResume roots workspace words meter'

/-- The original leaf call performs normalized GF64 root recovery, rejects
zero roots, and writes the exact active candidates before advancing. -/
def ActualRootLeaf : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter : WorkMeter),
    DirectTwo.CorrectArithmetic kernels →
    LeafBounds roots workspace →
    Roots.leaf DirectTwo.fieldDictionary kernels roots workspace meter =
      expectedLeaf roots workspace meter

end BulksketchBridge.RootLeaf
