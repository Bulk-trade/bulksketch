import Arithmetic.RootSetupGenerated
import BulksketchBridge.BmEntrySpec
import BulksketchBridge.ClosedLeafAdvanceSpec

namespace BulksketchBridge.RootSetup

open Aeneas.Std DenseCoefficient BmEntry RebuiltLfsr
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

def tableCount (degree : Nat) : Nat := degree * (degree / 2)

def workRegions (degree : Nat) (polynomials table : Slice U64)
    (raw : Slice RawProduct) (basis : SplitterBasis) : FactorWork :=
  let width := degree + 1
  let afterModulus := tail polynomials width
  let afterTrace := tail afterModulus degree
  ⟨prefixSlice polynomials width, prefixSlice afterModulus degree,
    prefixSlice afterTrace width, tail afterTrace width,
    prefixSlice table (tableCount degree), raw, basis⟩

def restoreWork (degree : Nat) (polynomials table : Slice U64) (later : FactorWork) :
    Slice U64 × Slice U64 × Slice RawProduct × SplitterBasis :=
  let width := degree + 1
  let afterModulus := tail polynomials width
  let afterTrace := tail afterModulus degree
  let rest := splitBack afterTrace width (later.gcd, later.work)
  let rest := splitBack afterModulus degree (later.trace, rest)
  (splitBack polynomials width (later.modulus, rest),
    restorePrefix table later.table, later.raw, later.basis)

/-- Exact borrowed scratch partition, including the function that restores
each later piece to its original caller. -/
def ActualFactorWork : Prop :=
  ∀ (degree : Usize) (polynomials table : Slice U64) (raw : Slice RawProduct)
    (basis : SplitterBasis),
    3 * degree.val + 2 ≤ polynomials.length →
    tableCount degree.val ≤ table.length →
    FactorWork.new degree polynomials table raw basis =
      .ok (workRegions degree.val polynomials table raw basis,
        restoreWork degree.val polynomials table)

def ActualRootConfiguration : Prop :=
  (∀ roots : Roots, Roots.enable_v3 roots = .ok { roots with v3 := true }) ∧
  (∀ roots : Roots, Roots.enable_closed_form roots = .ok { roots with closed_form := true }) ∧
  (∀ (roots : Roots) (seed : U64),
    Roots.set_splitter_seed roots seed = .ok { roots with splitter_seed := seed })

abbrev gf64Dictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

def startedRoots (roots : Roots) (degree : Usize) (affine : Bool) : Roots :=
  { roots with
    stride := ClosedLeafAdvance.usizeWord (degree.val + 1)
    degree := degree
    affine := affine
    affine_ready := false }

def startedWorkspace (degree : Usize) (workspace : RowWorkspace) : RowWorkspace :=
  { workspace with
    basis := ⟨none, 0#u32⟩
    polynomials := if degree = 0#usize then workspace.polynomials else
      restorePrefix workspace.polynomials (prefixSlice workspace.bm (degree.val + 1)) }

def RootStartBounds (degree : Usize) (workspace : RowWorkspace) : Prop :=
  degree.val + 1 ≤ Usize.max ∧
  (degree ≠ 0#usize →
    degree.val < workspace.polynomials.length ∧ degree.val < workspace.bm.length)

/-- Original start resets the row cache, copies exactly the nonzero-degree
locator prefix, and dispatches the updated state. Affine preference is
the exact original call and is skipped on the old protocol. -/
def ActualRootStart : Prop :=
  ∀ (roots : Roots) (degree : Usize) (workspace : RowWorkspace),
    RootStartBounds degree workspace →
    Roots.start roots degree workspace = (do
      let affine ← if roots.v3 then bulksketch.decode.affine.preferred gf64Dictionary degree
        else .ok false
      let updated := startedRoots roots degree affine
      .ok (ClosedLeafAdvance.stageFor updated, updated, startedWorkspace degree workspace, id))

end BulksketchBridge.RootSetup
