import BulksketchBridge.RootInvariantReborrow
import BulksketchBridge.RootTraversalFactor
import BulksketchBridge.RootDivideArena
import BulksketchBridge.RootDivideStages
import BulksketchBridge.NativeRootRun
import BulksketchBridge.RootNativeTraceDispatch

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std Algebra.Gf64 Polynomial SliceKernels DenseCoefficient RebuiltLfsr BmEntry
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

open RootDivide in
/-- A rejected assembly charge follows the original successful exact
    Dense division. It returns those scratch updates and leaves all live
    root and pending-factor state unchanged. -/
def ActualNativeDivideAssemblyChargeExit : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid failed : WorkMeter) (capacity budget : Nat) (error : DecodeError),
    RootTraversalInvariant locator roots workspace capacity budget →
    DenseDivRem.MulWordLaw kernels → DenseMulConvolutionSpec.RawMulAgrees kernels →
    DenseMul.reduceAgrees kernels → BmTerminal.NativeInverse kernels →
    charge meter (.Divide roots.degree) = .ok (.Ok (), paid) →
    charge paid (.SplitAssembly roots.degree) = .ok (.Err error, failed) →
    let buffers := buffersFor roots workspace
    let trace := slicePolynomial (prefixSlice buffers.trace roots.trace_len.val)
    ProperGcdFrame roots buffers trace →
    let call := nativeCall roots buffers
    let updated := afterCall roots buffers call.2.1 call.2.2.1 call.2.2.2
    let written := rebuild workspace roots updated
    Roots.run nativeCalls nativeDivRem dictionary kernels roots .FactorDivision workspace meter =
      .ok (.Err error, roots, written, id, failed) ∧
    RootTraversalInvariant locator roots written capacity budget ∧
    buffersFor roots written = updated ∧
    written.factors = workspace.factors ∧ written.stack = workspace.stack ∧
    written.roots = workspace.roots ∧ written.basis = workspace.basis

open RootDivide in
theorem native_divide_assembly_charge_exit : ActualNativeDivideAssemblyChargeExit := by
  intro K kernels locator roots workspace meter paid failed capacity budget error invariant mul rawLaw
    reduce inverse charged rejected buffers trace prior call updated written
  have bound := traversal_degree_budget locator roots workspace capacity budget invariant
  have minimum : 2 ≤ roots.degree.val := by have := prior.proper; omega
  obtain ⟨ready, modWidth, traceWidth, gcdWidth, _, _⟩ :=
    gcd_buffers_of_budget roots workspace capacity budget invariant.buffers minimum bound
  obtain ⟨divideReady, shape⟩ :=
    divide_ready_of_budget roots workspace capacity budget trace invariant.buffers bound prior
  have law := DenseDivRem.actual_native_div_rem kernels mul rawLaw reduce inverse
  obtain ⟨length, divided, _, _⟩ :=
    original_native_proper_gcd_call nativeDivRem kernels roots buffers trace law divideReady shape prior.gcdExact
  have failedCall :=
    assembly_charge_failure _ dictionary kernels roots buffers workspace.factors workspace.stack meter paid failed
      length call.2.1 call.2.2.1 call.2.2.2 error divideReady.workRoom divideReady.gcdRoom charged divided rejected
  have exactRun : Roots.run nativeCalls nativeDivRem dictionary kernels roots .FactorDivision workspace meter =
      .ok (.Err error, roots, written, id, failed) := by
    rw [original_root_run_refines kernels roots .FactorDivision workspace meter ready]
    unfold RootRun.expected
    rw [failedCall]
    simp only [bind_ok]
    rfl
  have workWidth : updated.work.length = workspace.polynomials.length - (roots.degree.val + 1) -
      roots.degree.val - (roots.degree.val + 1) := by
    unfold updated afterCall
    rw [splitBack_length]
    simp only [buffers, buffersFor, RootSetup.workRegions, tail_length]
  have tableWidth : updated.table.length = RootSetup.tableCount roots.degree.val := by
    change (prefixSlice workspace.square_table (RootSetup.tableCount roots.degree.val)).length = _
    rw [prefix_length, Nat.min_eq_left ready.2]
  have reborrow : buffersFor roots written = updated :=
    reborrow_factor_work roots workspace updated ready modWidth traceWidth gcdWidth workWidth tableWidth
  have rawWidth : updated.raw.length = workspace.raw.length := native_call_raw_width roots buffers
  have preserved : RootTraversalInvariant locator roots written capacity budget :=
    rebuild_preserves_traversal locator roots roots workspace updated capacity budget invariant
      rfl rfl rfl rfl rfl reborrow rfl rawWidth
  exact ⟨exactRun, preserved, reborrow, rfl, rfl, rfl, rfl⟩

open RootTrace DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec in
/-- A rejected split-check charge follows the original trace recurrence
    and cache extension. It preserves their exact returned work and does
    not advance or consume the live factor. -/
def ActualNativeTraceSplitChargeExit : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid failed : WorkMeter) (capacity budget : Nat) (error : DecodeError),
    RootTraversalInvariant locator roots workspace capacity budget →
    3 ≤ roots.degree.val → roots.checked = false → roots.attempts.val + 1 ≤ Usize.max →
    charge meter (.Trace roots.degree) = .ok (.Ok (), paid) →
    charge paid (.SplitCheck roots.degree) = .ok (.Err error, failed) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    let buffers := buffersFor roots workspace
    cacheWellFormed roots buffers →
    CorrectTable buffers.modulus buffers.table roots.degree.val →
    BackendSquareLaw kernels buffers.modulus buffers.table roots.degree.val →
    TraceAgreement (activeFactor roots workspace) roots.splitter_seed roots.direction.val →
    ∃ (attempts : Usize) (cacheLen : U32) (basis : Basis) (size : Usize)
      (trace gcd : Slice U64) (raw : Slice RawProduct),
      let after := { roots with attempts := attempts, trace_len := size }
      let updated := { buffers with trace, gcd, raw, basis := ⟨some basis, cacheLen⟩ }
      let written := rebuild workspace roots updated
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .Trace workspace meter =
        .ok (.Err error, after, written, id, failed) ∧
      RootTraversalInvariant locator after written capacity budget ∧
      buffersFor after written = updated ∧
      attempts.val = roots.attempts.val + 1 ∧
      cacheLen.val = max (cacheInitialLength buffers) (roots.direction.val + 1) ∧
      cachePrefix roots.splitter_seed basis cacheLen.val ∧
      size.val ≤ trace.length ∧
      traceInvariant buffers.modulus (basisWord roots.splitter_seed roots.direction.val) 64 size trace

open RootTrace DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec in
theorem native_trace_split_charge_exit : ActualNativeTraceSplitChargeExit := by
  intro K kernels locator roots workspace meter paid failed capacity budget error invariant minimum checked counter
    charged rejected rawLaw squareLaw reduce buffers cache correct backend agrees
  have bound := traversal_degree_budget locator roots workspace capacity budget invariant
  obtain ⟨ready, modWidth, traceWidth, gcdWidth, _, rawRoom⟩ :=
    gcd_buffers_of_budget roots workspace capacity budget invariant.buffers (by omega) bound
  have valid := invariant.active (by omega)
  have direction := trace_agreement_before_end (activeFactor roots workspace) roots.splitter_seed
    roots.direction.val valid.monic.ne_zero valid.split valid.simple (by rw [valid.exactDegree]; omega) agrees
  have tableWidth : buffers.table.length = RootSetup.tableCount roots.degree.val := by
    change (prefixSlice workspace.square_table (RootSetup.tableCount roots.degree.val)).length = _
    rw [prefix_length, Nat.min_eq_left ready.2]
  change buffers.modulus.length = roots.degree.val + 1 at modWidth
  change buffers.gcd.length = roots.degree.val + 1 at gcdWidth
  change 2 * (roots.degree.val + 2) ≤ buffers.raw.length at rawRoom
  have monic := traversal_monic_word locator roots workspace capacity budget invariant (by omega)
  have square := native_modular_square kernels rawLaw squareLaw reduce buffers.modulus buffers.table roots.degree.val
    (by omega) modWidth monic tableWidth correct backend
  change buffers.trace.length = roots.degree.val at traceWidth
  obtain ⟨attempts, cacheLen, basis, size, trace, gcd, raw, ran, attemptValue, _, cacheWidth, _, cacheData,
    traceRoom, traceLen, gcdLen, rawLen, meaningful⟩ :=
    trace_split_charge_failure nativeSquare kernels roots buffers meter paid failed error charged rejected checked counter
      direction cache (by omega) (by omega) (by omega) (by rw [traceWidth]; exact square)
  let after := { roots with attempts := attempts, trace_len := size }
  let updated := { buffers with trace, gcd, raw, basis := ⟨some basis, cacheLen⟩ }
  let written := rebuild workspace roots updated
  have exactRun : Roots.run nativeCalls nativeDivRem dictionary kernels roots .Trace workspace meter =
      .ok (.Err error, after, written, id, failed) := by
    rw [original_root_run_refines kernels roots .Trace workspace meter ready]
    unfold RootRun.expected
    rw [ran]
    simp only [bind_ok]
    rfl
  have workWidth : updated.work.length = workspace.polynomials.length - (roots.degree.val + 1) -
      roots.degree.val - (roots.degree.val + 1) := by
    simp only [updated, buffers, buffersFor, RootSetup.workRegions, tail_length]
  have reborrow : buffersFor after written = updated :=
    reborrow_factor_work roots workspace updated ready modWidth (traceLen.trans traceWidth)
      (gcdLen.trans gcdWidth) workWidth tableWidth
  have rawWidth : updated.raw.length = workspace.raw.length := rawLen
  have preserved : RootTraversalInvariant locator after written capacity budget :=
    rebuild_preserves_traversal locator roots after workspace updated capacity budget invariant
      rfl rfl rfl rfl rfl reborrow rfl rawWidth
  exact ⟨attempts, cacheLen, basis, size, trace, gcd, raw, exactRun, preserved, reborrow, attemptValue,
    cacheWidth, cacheData, traceRoom, meaningful⟩

#print axioms native_divide_assembly_charge_exit
#print axioms native_trace_split_charge_exit

end BulksketchBridge.RootRun
