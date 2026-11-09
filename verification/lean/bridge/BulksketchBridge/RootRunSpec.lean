import BulksketchBridge.RootRunGcd
import BulksketchBridge.AffineSubspaceStart

namespace BulksketchBridge.RootRun

open Aeneas.Std DenseCoefficient
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

abbrev Frame := Reply × Roots × RowWorkspace × (RowWorkspace → RowWorkspace) × WorkMeter
abbrev Calls := RootRunRuntime.OtherCallees
abbrev DivRem := DenseDivisionRuntime.DivRem
abbrev dictionary := BmTerminal.fieldDictionary

def buffersFor (roots : Roots) (workspace : RowWorkspace) : FactorWork :=
  RootSetup.workRegions roots.degree.val workspace.polynomials workspace.square_table workspace.raw workspace.basis

def frame (reply : Reply) (before after : Roots) (workspace : RowWorkspace)
    (buffers : FactorWork) (meter : WorkMeter) : Frame :=
  (reply, after, rebuild workspace before buffers, id, meter)

def tableStage (roots : Roots) : Stage :=
  if roots.affine then
    if roots.affine_ready then .AffineSplit else .AffinePreparation
  else .Trace

def affineStart (roots : Roots) : Nat :=
  roots.stride.val * roots.stride.val + subspaceStart (roots.affine_rank.val - 1)

def affineStop (roots : Roots) : Nat := affineStart roots + roots.affine_rank.val

def factorReady (roots : Roots) (workspace : RowWorkspace) : Prop :=
  3 * roots.degree.val + 2 ≤ workspace.polynomials.length ∧
  RootSetup.tableCount roots.degree.val ≤ workspace.square_table.length

def paidAffineReady (roots : Roots) (workspace : RowWorkspace) : Prop :=
  roots.affine_rank ≠ 0#usize → roots.affine_rank.val ≤ 64 ∧ affineStop roots ≤ workspace.factors.length

def paidGcdReady (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) : Prop :=
  let buffers := buffersFor roots workspace
  roots.trace_len.val ≤ roots.degree.val ∧
  ∃ size gcd work raw,
    bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into division dictionary kernels
      buffers.modulus (prefixSlice buffers.trace roots.trace_len.val) buffers.gcd buffers.work buffers.raw =
        .ok (size, gcd, work, raw) ∧ AfterGcdReady roots buffers size

/-- Admitted scratch for the stages that actually borrow FactorWork.
The split and GCD checks are needed only when the corresponding charge succeeds. -/
def Ready (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (stage : Stage) (workspace : RowWorkspace) (meter : WorkMeter) : Prop :=
  match stage with
  | .Leaf | .LeafThree | .LeafFour | .FactorVerification | .AffinePreparation | .AffineEnumeration => True
  | .AffineSplit => factorReady roots workspace ∧
      (∀ paid, charge meter (.AffineSplit roots.degree roots.affine_rank) = .ok (.Ok (), paid) →
        paidAffineReady roots workspace)
  | .Gcd => factorReady roots workspace ∧
      (∀ paid, charge meter (.Gcd roots.degree) = .ok (.Ok (), paid) →
        paidGcdReady division kernels roots workspace)
  | _ => factorReady roots workspace

def reducer {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter : WorkMeter) : Result Frame := do
  let buffers := buffersFor roots workspace
  let (charged, paid) ← charge meter (.Table roots.degree)
  match charged with
  | .Err reason => .ok (frame (.Err reason) roots roots workspace buffers paid)
  | .Ok () =>
    let (table, work) ← bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.prepare_square_table
      dictionary kernels buffers.modulus buffers.table buffers.work
    .ok (frame (.Ok (.Ok (tableStage roots))) roots roots workspace { buffers with table, work } paid)

def affineSplit {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter : WorkMeter) : Result Frame := do
  let buffers := buffersFor roots workspace
  let (charged, paid) ← charge meter (.AffineSplit roots.degree roots.affine_rank)
  match charged with
  | .Err reason => .ok (frame (.Err reason) roots roots workspace buffers paid)
  | .Ok () =>
    if roots.affine_rank = 0#usize then
      .ok (frame (.Ok (.Err .NotSplit)) roots roots workspace buffers paid)
    else do
      let subspaces := ClosedLeaf.region workspace.factors (affineStart roots) (affineStop roots)
      let (length, trace, work, raw) ← bulksketch.decode.affine.splitter
        bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into
        dictionary kernels buffers.modulus buffers.table subspaces roots.affine_base buffers.trace buffers.work buffers.raw
      .ok (frame (.Ok (.Ok .Gcd)) roots { roots with trace_len := length } workspace
        { buffers with trace, work, raw } paid)

def gcdStage (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter : WorkMeter) : Result Frame := do
  let buffers := buffersFor roots workspace
  let (charged, paid) ← charge meter (.Gcd roots.degree)
  match charged with
  | .Err reason => .ok (frame (.Err reason) roots roots workspace buffers paid)
  | .Ok () =>
    let (size, gcd, work, raw) ← bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.monic_gcd_into
      division dictionary kernels buffers.modulus (prefixSlice buffers.trace roots.trace_len.val)
      buffers.gcd buffers.work buffers.raw
    let (reply, updated) := outcome roots buffers size
    .ok (frame reply roots updated workspace { buffers with gcd, work, raw } paid)

/-- Independent stage dispatch and full returned row frame. Bound native
callees are named directly and the remaining affine slots are explicit. -/
def expected (calls : Calls) (division : DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (stage : Stage) (workspace : RowWorkspace) (meter : WorkMeter) : Result Frame :=
  match stage with
  | .LeafThree | .LeafFour | .FactorVerification => Roots.closed_leaf dictionary kernels roots stage workspace meter
  | .Leaf => Roots.leaf dictionary kernels roots workspace meter
  | .AffinePreparation => Roots.prepare_affine calls.preparation dictionary kernels roots workspace meter
  | .AffineEnumeration => Roots.enumerate_affine bulksketch.decode.affine.enumerate dictionary kernels roots workspace meter
  | .ReducerPreparation => reducer kernels roots workspace meter
  | .AffineSplit => affineSplit kernels roots workspace meter
  | .Gcd => gcdStage division kernels roots workspace meter
  | .Trace => do
      let (reply, updated, buffers, back, paid) ← Roots.trace
        bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into dictionary kernels
        roots (buffersFor roots workspace) meter
      .ok (frame reply roots updated workspace (back buffers) paid)
  | .FactorDivision => do
      let (reply, updated, buffers, back, factors, stack, paid) ←
        Roots.divide (bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.exact_divide_into division)
          dictionary kernels roots (buffersFor roots workspace) workspace.factors workspace.stack meter
      let w := rebuild workspace roots (back buffers)
      .ok (reply, updated, { w with factors, stack }, id, paid)
  | _ => .fail .panic

def ActualRootRun : Prop :=
  ∀ (calls : Calls) (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (stage : Stage) (workspace : RowWorkspace) (meter : WorkMeter),
    Ready division kernels roots stage workspace meter →
    Roots.run calls division dictionary kernels roots stage workspace meter =
      expected calls division kernels roots stage workspace meter

end BulksketchBridge.RootRun
