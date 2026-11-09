import BulksketchBridge.RootWorkspaceBudget
import BulksketchBridge.DenseGcd

namespace BulksketchBridge.RootRun

open Aeneas.Std DenseCoefficient BmEntry RebuiltLfsr
open bulksketch.decode.roots bulksketch.decode.scratch

private theorem splitBack_reborrow (original left right : Slice U64) (split : Nat)
    (room : split ≤ original.length) (leftLen : left.length = split)
    (rightLen : right.length = original.length - split) :
    prefixSlice (splitBack original split (left, right)) split = left ∧
      tail (splitBack original split (left, right)) split = right := by
  have lengths : left.length = min split original.length ∧ right.length = original.length - split :=
    ⟨by rwa [Nat.min_eq_left room], rightLen⟩
  rw [splitBack, dite_eq_left lengths]
  constructor
  · apply Slice.ext
    simp only [prefixSlice, Slice.from_val, ← leftLen]
    exact List.take_left
  · apply Slice.ext
    simp only [tail, Slice.from_val, ← leftLen]
    exact List.drop_left

/-- Reborrow the exact original FactorWork windows after the native
backward frame. The next trace or GCD stage sees exactly the slices
returned by the previous one. -/
theorem reborrow_factor_work (roots : Roots) (workspace : RowWorkspace) (later : FactorWork)
    (ready : factorReady roots workspace)
    (modulus : later.modulus.length = roots.degree.val + 1)
    (trace : later.trace.length = roots.degree.val)
    (gcd : later.gcd.length = roots.degree.val + 1)
    (work : later.work.length = workspace.polynomials.length - (roots.degree.val + 1) -
      roots.degree.val - (roots.degree.val + 1))
    (table : later.table.length = RootSetup.tableCount roots.degree.val) :
    buffersFor roots (rebuild workspace roots later) = later := by
  let width := roots.degree.val + 1
  let afterModulus := tail workspace.polynomials width
  let afterTrace := tail afterModulus roots.degree.val
  let restGcd := splitBack afterTrace width (later.gcd, later.work)
  let restTrace := splitBack afterModulus roots.degree.val (later.trace, restGcd)
  have widthFits : width ≤ workspace.polynomials.length := by have := ready.1; omega
  have afterModulusLength : afterModulus.length = workspace.polynomials.length - width := tail_length ..
  have afterTraceLength : afterTrace.length = workspace.polynomials.length - width - roots.degree.val := by
    rw [show afterTrace = tail afterModulus roots.degree.val from rfl, tail_length, afterModulusLength]
  have workLength : later.work.length = afterTrace.length - width := by rw [afterTraceLength]; exact work
  have traceRoom : roots.degree.val ≤ afterModulus.length := by
    rw [afterModulusLength]
    have := ready.1
    omega
  have gcdRoom : width ≤ afterTrace.length := by rw [afterTraceLength]; have := ready.1; omega
  have restGcdLength : restGcd.length = afterModulus.length - roots.degree.val :=
    (splitBack_length ..).trans (tail_length ..)
  have restTraceLength : restTrace.length = workspace.polynomials.length - width :=
    (splitBack_length ..).trans afterModulusLength
  obtain ⟨exactModulus, exactRestTrace⟩ :=
    splitBack_reborrow workspace.polynomials later.modulus restTrace width widthFits modulus restTraceLength
  obtain ⟨exactTrace, exactRestGcd⟩ :=
    splitBack_reborrow afterModulus later.trace restGcd roots.degree.val traceRoom trace restGcdLength
  obtain ⟨exactGcd, exactWork⟩ := splitBack_reborrow afterTrace later.gcd later.work width gcdRoom gcd workLength
  have exactTable : prefixSlice (restorePrefix workspace.square_table later.table)
      (RootSetup.tableCount roots.degree.val) = later.table := by
    rw [← table, DenseGcd.prefix_restored]
    exact table.trans_le ready.2
  change
    (⟨prefixSlice (splitBack workspace.polynomials width (later.modulus, restTrace)) width,
      prefixSlice (tail (splitBack workspace.polynomials width (later.modulus, restTrace)) width) roots.degree.val,
      prefixSlice (tail (tail (splitBack workspace.polynomials width (later.modulus, restTrace)) width) roots.degree.val) width,
      tail (tail (tail (splitBack workspace.polynomials width (later.modulus, restTrace)) width) roots.degree.val) width,
      prefixSlice (restorePrefix workspace.square_table later.table) (RootSetup.tableCount roots.degree.val), later.raw, later.basis⟩
      : FactorWork) = later
  rw [exactModulus, exactRestTrace, exactTrace, exactRestGcd, exactGcd, exactWork, exactTable]

#print axioms reborrow_factor_work

end BulksketchBridge.RootRun
