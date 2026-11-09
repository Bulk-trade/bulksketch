import BulksketchBridge.RootTraceField
import BulksketchBridge.RootTraceGenerator
import BulksketchBridge.RootRunGcd
import BulksketchBridge.RootAffineChildren

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial RootTrace DenseCoefficient SliceKernels
open bulksketch.decode.roots bulksketch.decode.scratch

set_option maxRecDepth 4096

noncomputable def traceBit (seed : U64) (direction : Nat) (point : Field) : ZMod 2 :=
  Algebra.trace (ZMod 2) Field (toField (basisWord seed direction).bv * point)

/-- Every earlier trace direction is constant on the current factor.
A proper division keeps the selected side; a retry retains the whole factor. -/
def TraceAgreement (factor : Polynomial Field) (seed : U64) (direction : Nat) : Prop :=
  ∀ earlier < direction, ∀ left right, factor.IsRoot left → factor.IsRoot right →
    traceBit seed earlier left = traceBit seed earlier right

theorem trace_agreement_of_dvd (factor child : Polynomial Field) (seed : U64) (direction : Nat)
    (divides : child ∣ factor) (same : TraceAgreement factor seed direction) :
    TraceAgreement child seed direction := by
  intro earlier bound left right leftRoot rightRoot
  apply same earlier bound left right
  · exact (dvd_iff_isRoot).mp ((dvd_iff_isRoot.mpr leftRoot).trans divides)
  · exact (dvd_iff_isRoot).mp ((dvd_iff_isRoot.mpr rightRoot).trans divides)

private theorem gcd_root (factor trace : Polynomial Field) (point : Field) :
    (gcd factor trace).IsRoot point ↔ factor.IsRoot point ∧ trace.IsRoot point := by
  simp only [← dvd_iff_isRoot, dvd_gcd_iff]

theorem nonproper_trace_agrees (factor trace : Polynomial Field) (seed : U64) (direction : Nat)
    (monic : factor.Monic)
    (notProper : ¬ (0 < (gcd factor trace).natDegree ∧ (gcd factor trace).natDegree < factor.natDegree))
    (exact : ∀ point, factor.IsRoot point → (trace.IsRoot point ↔ traceBit seed direction point = 0)) :
    ∀ left right, factor.IsRoot left → factor.IsRoot right →
      traceBit seed direction left = traceBit seed direction right := by
  have gcdNonzero : gcd factor trace ≠ 0 :=
    fun zero => monic.ne_zero ((gcd_eq_zero_iff factor trace).mp zero).1
  by_cases constant : (gcd factor trace).natDegree = 0
  · have nonzeroBit (point : Field) (root : factor.IsRoot point) : traceBit seed direction point ≠ 0 := by
      intro zero
      have gRoot := (gcd_root factor trace point).mpr ⟨root, (exact point root).mpr zero⟩
      have present := (mem_roots gcdNonzero).mpr gRoot
      have positive := Multiset.card_pos_iff_exists_mem.mpr ⟨point, present⟩
      have bound := card_roots' (gcd factor trace)
      omega
    intro left right leftRoot rightRoot
    have bit : ∀ value : ZMod 2, value = 0 ∨ value = 1 := by decide
    rw [(bit _).resolve_left (nonzeroBit left leftRoot), (bit _).resolve_left (nonzeroBit right rightRoot)]
  · have fullDegree : factor.natDegree ≤ (gcd factor trace).natDegree := by omega
    have gcdMonic := (normalize_eq_self_iff_monic gcdNonzero).mp (normalize_gcd factor trace)
    have full : factor = gcd factor trace :=
      eq_of_monic_of_dvd_of_natDegree_le gcdMonic monic (gcd_dvd_left factor trace) fullDegree
    intro left right leftRoot rightRoot
    have traceZero (point : Field) (root : factor.IsRoot point) : traceBit seed direction point = 0 :=
      (exact point root).mp ((gcd_root factor trace point).mp (full ▸ root)).2
    rw [traceZero left leftRoot, traceZero right rightRoot]

/-- The original 64-step trace evaluates to the binary trace at each
factor root, so its zero test classifies that root by its cached direction. -/
theorem trace_invariant_classifies (modulus trace : Slice U64) (length : Usize)
    (seed : U64) (direction : Nat)
    (invariant : traceInvariant modulus (basisWord seed direction) 64 length trace) :
    ∀ point, (slicePolynomial modulus).IsRoot point →
      ((slicePolynomial (prefixSlice trace length.val)).IsRoot point ↔ traceBit seed direction point = 0) := by
  intro point root
  change (slicePolynomial (prefixSlice trace length.val)).eval point = 0 ↔ _
  rw [invariant point root, trace_at_is_algebra_trace]
  change algebraMap (ZMod 2) Field (traceBit seed direction point) = 0 ↔ _
  rw [← (algebraMap (ZMod 2) Field).map_zero, (algebraMap (ZMod 2) Field).injective.eq_iff]

/-- A successful trace split fixes the current trace bit on each child
and preserves every preceding direction. -/
theorem trace_agreement_after_division (factor trace left right : Polynomial Field)
    (seed : U64) (direction : Nat) (simple : Squarefree factor)
    (gcdExact : left = gcd factor trace) (product : factor = right * left)
    (prior : TraceAgreement factor seed direction)
    (classifies : ∀ point, factor.IsRoot point → (trace.IsRoot point ↔ traceBit seed direction point = 0)) :
    TraceAgreement left seed (direction + 1) ∧ TraceAgreement right seed (direction + 1) := by
  have leftPrior := trace_agreement_of_dvd factor left seed direction
    (by rw [product]; exact dvd_mul_left _ _) prior
  have rightPrior := trace_agreement_of_dvd factor right seed direction
    (by rw [product]; exact dvd_mul_right _ _) prior
  have leftZero (point : Field) (root : left.IsRoot point) : traceBit seed direction point = 0 := by
    have parent := (RootDivide.gcd_quotient_root_partition factor trace left right simple gcdExact product point).1.mp root
    exact (classifies point parent.1).mp parent.2
  have rightOne (point : Field) (root : right.IsRoot point) : traceBit seed direction point = 1 := by
    have parent := (RootDivide.gcd_quotient_root_partition factor trace left right simple gcdExact product point).2.mp root
    have bit : ∀ value : ZMod 2, value = 0 ∨ value = 1 := by decide
    exact (bit _).resolve_left fun zero => parent.2 ((classifies point parent.1).mpr zero)
  constructor
  · intro index bound x y hx hy
    by_cases earlier : index < direction
    · exact leftPrior index earlier x y hx hy
    · rw [show index = direction by omega, leftZero x hx, leftZero y hy]
  · intro index bound x y hx hy
    by_cases earlier : index < direction
    · exact rightPrior index earlier x y hx hy
    · rw [show index = direction by omega, rightOne x hx, rightOne y hy]

theorem trace_agreement_before_end (factor : Polynomial Field) (seed : U64) (direction : Nat)
    (nonzero : factor ≠ 0) (split : factor.Splits) (simple : factor.roots.Nodup)
    (degree : 2 ≤ factor.natDegree) (same : TraceAgreement factor seed direction) : direction < 64 := by
  classical
  have size : 1 < factor.roots.toFinset.card := by
    rw [Multiset.toFinset_card_of_nodup simple, ← split.natDegree_eq_card_roots]
    omega
  obtain ⟨left, right, leftMem, rightMem, different⟩ := Finset.one_lt_card_iff.mp size
  have leftRoot := (mem_roots nonzero).mp (Multiset.mem_toFinset.mp leftMem)
  have rightRoot := (mem_roots nonzero).mp (Multiset.mem_toFinset.mp rightMem)
  obtain ⟨index, bounded, separates⟩ := some_cached_direction_separates seed left right different
  by_contra! exhausted
  exact separates (same index (by omega) left right leftRoot rightRoot)

/-- A nonproper GCD after the original trace cannot consume the final
direction on a split simple factor of degree at least two. Its actual
outcome is a bounded retry and extends trace agreement by one. -/
def ActualTraceGcdRetry : Prop :=
  ∀ (roots : Roots) (buffers : FactorWork) (size : Usize) (factor trace : Polynomial Field),
    roots.affine = false → factor.Monic → factor.Splits → factor.roots.Nodup →
    2 ≤ factor.natDegree → factor.natDegree = roots.degree.val →
    size.val = (gcd factor trace).natDegree + 1 → ¬ Proper roots size →
    TraceAgreement factor roots.splitter_seed roots.direction.val →
    (∀ point, factor.IsRoot point → (trace.IsRoot point ↔
      traceBit roots.splitter_seed roots.direction.val point = 0)) →
    let next := outcome roots buffers size
    next.1 = .Ok (.Ok .Trace) ∧
    next.2.direction.val = roots.direction.val + 1 ∧ next.2.direction.val < 64 ∧
    TraceAgreement factor roots.splitter_seed next.2.direction.val

theorem trace_gcd_retry : ActualTraceGcdRetry := by
  intro roots buffers size factor trace affine monic split simple degree degreeValue sizeValue notProper same exactTrace
  have nonProper : ¬ (0 < size.val - 1 ∧ size.val - 1 < roots.degree.val) := notProper
  have agree := nonproper_trace_agrees factor trace roots.splitter_seed roots.direction.val monic (by omega) exactTrace
  have extended : TraceAgreement factor roots.splitter_seed (roots.direction.val + 1) := by
    intro index indexBound left right leftRoot rightRoot
    by_cases earlier : index < roots.direction.val
    · exact same index earlier left right leftRoot rightRoot
    · rw [show index = roots.direction.val by omega]
      exact agree left right leftRoot rightRoot
  have remaining := trace_agreement_before_end factor roots.splitter_seed (roots.direction.val + 1)
    monic.ne_zero split simple degree extended
  have direction : (nextDirection roots).val = roots.direction.val + 1 := by
    change (BitVec.ofNat 32 (roots.direction.val + 1)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have notEnd : nextDirection roots ≠ 64#u32 := by
    intro last
    rw [last] at direction
    change 64 = _ at direction
    omega
  unfold outcome
  simp only [nonProper, ite_false, affine, Bool.false_eq_true, notEnd, direction]
  exact ⟨trivial, trivial, remaining, extended⟩

#print axioms trace_gcd_retry

end BulksketchBridge.RootRun
