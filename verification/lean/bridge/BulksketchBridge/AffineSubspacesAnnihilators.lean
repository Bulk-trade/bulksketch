import BulksketchBridge.AffineSubspacesPolynomial
import BulksketchBridge.AffineSubspaceAlgebra

namespace BulksketchBridge.AffineSubspaces

open Aeneas Aeneas.Std
open AffineLinearEval Algebra.Gf64 Polynomial BulksketchBridge.AffineSubspaceAlgebra
open bulksketch.decode.affine bulksketch.backend.contract

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

/-- Reverse direction order matches the inductive definition of annihilator. -/
noncomputable def prefixDirections (basis : Slice U64) : Nat → List Field
  | 0 => []
  | rank + 1 => toField basis[rank]!.bv :: prefixDirections basis rank

def ExactThrough (basis table : Slice U64) (rank : Nat) : Prop :=
  ∀ rowRank, rowRank ≤ rank →
    rowPolynomial (row table rowRank) = annihilator (prefixDirections basis rowRank)

private theorem initial_exact (basis table : Slice U64) (room : 0 < table.length) :
    ExactThrough basis (table.setAtNat 0 1#u64) 0 := by
  intro rank rankZero
  have exactZero : rank = 0 := by omega
  subst rank
  have sameLength := Slice.setAtNat_length table 0 1#u64
  have rowRoom : offset (0 + 1) ≤ (table.setAtNat 0 1#u64).length := by
    rw [sameLength]; exact room
  have coefficient : (row (table.setAtNat 0 1#u64) 0)[0]! = 1#u64 := by
    rw [row_read _ 0 0 rowRoom (by decide)]
    change (table.setAtNat 0 1#u64)[0]! = _
    simpa only [Slice.getElem!_Nat_eq] using Slice.getElem!_Nat_setAtNat_eq table 0 1#u64 room
  simp only [rowPolynomial, row_length _ 0 rowRoom, Nat.zero_add, Finset.sum_range_one, coefficient,
    show toField (1#u64).bv = 1 from toField_one, map_one, pow_zero, pow_one, one_mul,
    prefixDirections, annihilator]

private theorem earlier_rows {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (table updated : Slice U64) (rank rowRank : Nat)
    (direction : U64) (room : offset (rank + 1 + 1) ≤ table.length)
    (earlier : rowRank ≤ rank) (ran : tableStep kernels table rank direction = .ok updated) :
    rowPolynomial (row updated rowRank) = rowPolynomial (row table rowRank) := by
  obtain ⟨sameLength, _, frame⟩ :=
    tableStep_coefficients kernels arithmetic table updated rank direction room ran
  have tableRoom : offset (rowRank + 1) ≤ table.length := (offset_mono (by omega)).trans room
  have resultRoom : offset (rowRank + 1) ≤ updated.length := by rwa [sameLength]
  simp only [rowPolynomial, row_length _ _ tableRoom, row_length _ _ resultRoom]
  apply Finset.sum_congr rfl
  intro position hp
  have bounded := Finset.mem_range.mp hp
  rw [row_read _ _ _ resultRoom bounded, row_read _ _ _ tableRoom bounded]
  rw [frame (offset rowRank + position) (Or.inl (by
    have ending := offset_succ rowRank
    have nextBefore : offset (rowRank + 1) ≤ offset (rank + 1) := offset_mono (by omega)
    omega))]

private theorem step_exact {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (basis table updated : Slice U64) (rank : Nat)
    (room : offset (rank + 1 + 1) ≤ table.length) (prior : ExactThrough basis table rank)
    (ran : tableStep kernels table rank basis[rank]! = .ok updated) :
    ExactThrough basis updated (rank + 1) := by
  intro rowRank admitted
  by_cases earlier : rowRank ≤ rank
  · rw [earlier_rows kernels arithmetic table updated rank rowRank basis[rank]! room earlier ran]
    exact prior rowRank earlier
  · have next : rowRank = rank + 1 := by omega
    subst rowRank
    rw [tableStep_polynomial kernels arithmetic table updated rank basis[rank]! room ran,
      prior rank (by omega)]
    rfl

theorem tableFold_annihilators {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (basis table updated : Slice U64) (rank count : Nat)
    (room : offset (rank + count + 1) ≤ table.length)
    (prior : ExactThrough basis table rank)
    (ran : tableFold kernels basis table rank count = .ok updated) :
    ExactThrough basis updated (rank + count) := by
  induction count generalizing table rank with
  | zero =>
    simp only [tableFold, Result.ok.injEq] at ran
    subst updated
    exact prior
  | succ count ih =>
    have stepRoom : offset (rank + 1 + 1) ≤ table.length := (offset_mono (by omega)).trans room
    obtain ⟨directionValue, evaluated, _⟩ :=
      linear_eval_refines kernels (row table rank) basis[rank]! arithmetic
    let next := table.setSlice! (offset (rank + 1))
      (nextRow (row table rank) (row table (rank + 1)) directionValue).val
    have step : tableStep kernels table rank basis[rank]! = .ok next := by
      simp only [tableStep, evaluated, bind_ok, next]
    have length : next.length = table.length := Slice.setSlice!_length ..
    have nextRoom : offset (rank + 1 + count + 1) ≤ next.length := by
      rw [length, show rank + 1 + count + 1 = rank + (count + 1) + 1 by omega]
      exact room
    have nextRan : tableFold kernels basis next (rank + 1) count = .ok updated := by
      simpa only [tableFold, step, bind_ok] using ran
    have nextExact := step_exact kernels arithmetic basis table next rank stepRoom prior step
    have exactFinal := ih next (rank + 1) nextRoom nextExact nextRan
    rwa [show rank + 1 + count = rank + (count + 1) by omega] at exactFinal

/-- The complete original routine returns all prefix annihilators and
preserves the scratch-table length. -/
theorem subspaces_annihilators {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (basis table : Slice U64)
    (rankBound : basis.length ≤ 64) (room : offset (basis.length + 1) ≤ table.length) :
    ∃ updated, subspaces fieldDictionary kernels basis table = .ok updated ∧
      updated.length = table.length ∧ ExactThrough basis updated basis.length := by
  obtain ⟨updated, normal, foldNormal, length⟩ :=
    subspaces_refines kernels arithmetic basis table rankBound room
  have positive : 0 < table.length := by
    have first : offset 1 ≤ offset (basis.length + 1) := offset_mono (by omega)
    change 1 ≤ offset (basis.length + 1) at first
    omega
  have fitted : offset (0 + basis.length + 1) ≤ (table.setAtNat 0 1#u64).length := by
    simpa only [Nat.zero_add, Slice.setAtNat_length] using room
  refine ⟨updated, normal, length, ?_⟩
  simpa only [Nat.zero_add] using
    tableFold_annihilators kernels arithmetic basis (table.setAtNat 0 1#u64) updated
      0 basis.length fitted (initial_exact basis table positive) foldNormal

def ActualSubspacesZeroSet : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    CorrectArithmetic kernels → ∀ (basis table : Slice U64),
    basis.length ≤ 64 → offset (basis.length + 1) ≤ table.length →
    ∃ updated, subspaces fieldDictionary kernels basis table = .ok updated ∧
      ∀ rank, rank ≤ basis.length → ∀ point : Field,
        (rowPolynomial (row updated rank)).eval point = 0 ↔
          point ∈ spanWords (prefixDirections basis rank)

theorem subspaces_zero_set : ActualSubspacesZeroSet := by
  intro K kernels arithmetic basis table rankBound room
  obtain ⟨updated, normal, _, exactRows⟩ :=
    subspaces_annihilators kernels arithmetic basis table rankBound room
  refine ⟨updated, normal, ?_⟩
  intro rank admitted point
  rw [exactRows rank admitted]
  exact annihilator_zero _ _

end BulksketchBridge.AffineSubspaces
