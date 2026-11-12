import BulksketchBridge.RootDivideGcdExact
import BulksketchBridge.RootTraversalPotential
import BulksketchBridge.RootWorkspaceBudget

namespace BulksketchBridge.RootDivide

open Aeneas.Std RootRun DenseCoefficient RebuiltLfsr BmEntry SliceKernels Algebra.Gf64 Polynomial
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- The live polynomial and native GCD result at the FactorDivision stage.
The coefficient count is the one returned by the original Dense GCD call. -/
structure ProperGcdFrame (roots : Roots) (buffers : FactorWork) (trace : Polynomial Field) : Prop where
  monic : (slicePolynomial buffers.modulus).Monic
  normalized : (slicePolynomial buffers.modulus).natDegree = roots.degree.val
  gcdExact : slicePolynomial (prefixSlice buffers.gcd roots.gcd_len.val) =
    gcd (slicePolynomial buffers.modulus) trace
  length : roots.gcd_len.val = roots.gcd_degree.val + 1
  gcdDegree : roots.gcd_degree.val = (gcd (slicePolynomial buffers.modulus) trace).natDegree
  proper : 0 < roots.gcd_degree.val ∧ roots.gcd_degree.val < roots.degree.val

/-- Derive the native div/rem scratch and leading-coefficient checks from
the admitted row budget and the original GCD's normalized polynomial. -/
theorem divide_ready_of_budget (roots : Roots) (workspace : RowWorkspace)
    (capacity budget : Nat) (trace : Polynomial Field)
    (sized : BudgetBuffers workspace capacity budget) (degreeBound : roots.degree.val ≤ budget)
    (prior : ProperGcdFrame roots (buffersFor roots workspace) trace) :
    NativeDivideReady roots (buffersFor roots workspace) ∧
      ProperDivideShape roots (buffersFor roots workspace) := by
  let buffers := buffersFor roots workspace
  have degreeMin : 2 ≤ roots.degree.val := by
    obtain ⟨positive, proper⟩ := prior.proper
    omega
  obtain ⟨_, modulusWidth, _, gcdWidth, workWidth, rawWidth⟩ :=
    gcd_buffers_of_budget roots workspace capacity budget sized degreeMin degreeBound
  change buffers.modulus.length = roots.degree.val + 1 at modulusWidth
  change buffers.gcd.length = roots.degree.val + 1 at gcdWidth
  change 4 * (roots.degree.val + 2) ≤ buffers.work.length at workWidth
  change 2 * (roots.degree.val + 2) ≤ buffers.raw.length at rawWidth
  have count := prior.length
  have ⟨gcdPositive, gcdProper⟩ := prior.proper
  have gcdRoom : roots.gcd_len.val ≤ buffers.gcd.length := by omega
  have gcdPrefixLen : (prefixSlice buffers.gcd roots.gcd_len.val).length = roots.gcd_len.val :=
    (prefix_length _ _).trans (Nat.min_eq_left gcdRoom)
  let divisor := gcd (slicePolynomial buffers.modulus) trace
  have divisorNonzero : divisor ≠ 0 :=
    fun zero => prior.monic.ne_zero ((gcd_eq_zero_iff _ _).mp zero).1
  have divisorMonic : divisor.Monic :=
    (normalize_eq_self_iff_monic divisorNonzero).mp (normalize_gcd _ _)
  have modulusLeading : buffers.modulus[buffers.modulus.length - 1]! ≠ 0#u64 := by
    intro zero
    have lead : (slicePolynomial buffers.modulus).leadingCoeff = 1 := prior.monic
    rw [leadingCoeff, prior.normalized, slicePolynomial_coeff, ite_eq_left (by omega),
      show roots.degree.val = buffers.modulus.length - 1 by omega, zero] at lead
    change toField (0 : BitVec 64) = 1 at lead
    rw [toField_zero] at lead
    exact zero_ne_one lead
  have gcdExact : slicePolynomial (prefixSlice buffers.gcd roots.gcd_len.val) =
      gcd (slicePolynomial buffers.modulus) trace := prior.gcdExact
  have gcdLeading : (prefixSlice buffers.gcd roots.gcd_len.val)[roots.gcd_len.val - 1]! ≠ 0#u64 := by
    intro zero
    have lead : divisor.leadingCoeff = 1 := divisorMonic
    change (gcd (slicePolynomial buffers.modulus) trace).leadingCoeff = 1 at lead
    rw [leadingCoeff, ← prior.gcdDegree, ← gcdExact, slicePolynomial_coeff, ite_eq_left (by omega),
      show roots.gcd_degree.val = roots.gcd_len.val - 1 by omega, zero] at lead
    change toField (0 : BitVec 64) = 1 at lead
    rw [toField_zero] at lead
    exact zero_ne_one lead
  change NativeDivideReady roots buffers ∧ ProperDivideShape roots buffers
  refine ⟨⟨⟨?_, gcdRoom⟩, ?_, gcdLeading, ?_, ?_, ?_⟩,
    ⟨modulusWidth, modulusLeading, count, gcdPositive, gcdProper⟩⟩ <;> omega

/-- The actual native checked offsets succeed from the live degree budget.
The quotient leaves the reserved affine base cell outside its prefix. -/
theorem divide_commit_of_budget (roots : Roots) (workspace : RowWorkspace)
    (capacity budget : Nat) (buffers : FactorWork) (length : Usize)
    (sized : BudgetBuffers workspace capacity budget)
    (strideBound : roots.stride.val ≤ budget + 1) (activeWidth : roots.degree.val < roots.stride.val)
    (positiveSlots : ∀ slot < roots.pending.val, 0 < slotDegree workspace.stack slot)
    (mass : factorDegreeMass roots workspace.stack ≤ budget)
    (direction : roots.direction.val + 1 ≤ U32.max)
    (rank : roots.affine = true → 0 < roots.affine_rank.val ∧ roots.affine_rank.val ≤ 64)
    (basis : roots.affine = true → ∃ directions, buffers.basis.directions = some directions)
    (ready : NativeDivideReady roots buffers) (shape : ProperDivideShape roots buffers)
    (candidate : (nativeCall roots buffers).1 = some length) :
    ∃ start stop : Usize,
      Usize.checked_mul roots.pending roots.stride = some start ∧
      Usize.checked_add start length = some stop ∧
      start.val = roots.pending.val * roots.stride.val ∧
      length.val < roots.stride.val ∧
      (roots.pending.val + 1) * roots.stride.val ≤ workspace.factors.length ∧
      CommitReady roots buffers workspace.factors workspace.stack (nativeCall roots buffers).2.1 length start stop := by
  obtain ⟨positive, quotientRoom, _, degree, _⟩ := native_call_degree roots buffers ready shape length candidate
  have gcdPositive := shape.gcdPositive
  have lengthRoom : length.val < roots.stride.val := by omega
  obtain ⟨stackRoom, factorRoom⟩ :=
    commit_slot_of_budget roots workspace capacity budget sized strideBound (by omega) positiveSlots mass
  have advance : (roots.pending.val + 1) * roots.stride.val =
      roots.pending.val * roots.stride.val + roots.stride.val := by rw [Nat.add_mul, Nat.one_mul]
  have startFits : roots.pending.val * roots.stride.val ≤ Usize.max := by
    have factorsFit : workspace.factors.length ≤ Usize.max := workspace.factors.length_ineq
    rw [advance] at factorRoom
    omega
  have startSpec := Usize.checked_mul_bv_spec roots.pending roots.stride
  cases startEq : Usize.checked_mul roots.pending roots.stride with
  | none =>
    rw [startEq] at startSpec
    exact (Nat.not_lt_of_ge startFits startSpec).elim
  | some start =>
    rw [startEq] at startSpec
    have startVal := startSpec.2.1
    have lastRoom : start.val + roots.stride.val ≤ workspace.factors.length := by rwa [advance, ← startVal] at factorRoom
    have stopFits : start.val + length.val ≤ Usize.max := by
      have fits : workspace.factors.length ≤ Usize.max := workspace.factors.length_ineq
      omega
    have stopSpec := Usize.checked_add_bv_spec start length
    cases stopEq : Usize.checked_add start length with
    | none =>
      rw [stopEq] at stopSpec
      exact (Nat.not_lt_of_ge stopFits stopSpec).elim
    | some stop =>
      rw [stopEq] at stopSpec
      have stopVal := stopSpec.2.1
      refine ⟨start, stop, rfl, stopEq, startVal, lengthRoom, factorRoom,
        ⟨by omega, quotientRoom, by omega, ?_, direction, rank, basis, fun _ => ⟨by omega, lastRoom⟩⟩⟩
      have divisorWidth := shape.gcdWidth
      have modulusWidth := shape.modulusWidth
      have proper := shape.proper
      omega

end BulksketchBridge.RootDivide
