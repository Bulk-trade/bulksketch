import BulksketchBridge.AffineSolveMap
import BulksketchBridge.AffineSolveMapGraph
import BulksketchBridge.AffineSolveMapColumnMeaning
import BulksketchBridge.Algebra.WordEquiv
import Mathlib.Algebra.CharP.Lemmas

namespace BulksketchBridge.AffineSolveMap

open Aeneas Aeneas.Std Algebra.Gf64 FrobeniusTables
open bulksketch.backend.contract bulksketch.decode.affine
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

noncomputable def linearWord (coefficients : Slice U64) (word : U64) : U64 :=
  ⟨wordFieldEquiv.symm (AffineLinearEval.linearValueFrom coefficients word 0)⟩

theorem linear_word_field (coefficients : Slice U64) (word : U64) :
    toField (linearWord coefficients word).bv = AffineLinearEval.linearValueFrom coefficients word 0 := by
  change wordFieldEquiv (wordFieldEquiv.symm _) = _
  exact wordFieldEquiv.apply_symm_apply _

theorem linear_word_additive (coefficients : Slice U64) : XorLinear (linearWord coefficients) := by
  constructor
  · apply U64.bv_eq_imp_eq
    apply toField_injective
    rw [linear_word_field, show toField (0#u64).bv = 0 from toField_zero]
    unfold AffineLinearEval.linearValueFrom
    apply Finset.sum_eq_zero
    intro offset _
    have exponent : 2 ^ (0 + offset) ≠ 0 := by positivity
    rw [show toField (0#u64).bv = 0 from toField_zero,
      zero_pow exponent, mul_zero]
  · intro left right
    apply U64.bv_eq_imp_eq
    apply toField_injective
    change toField (linearWord coefficients (left ^^^ right)).bv =
      toField ((linearWord coefficients left).bv ^^^ (linearWord coefficients right).bv)
    rw [toField_xor, linear_word_field, linear_word_field, linear_word_field]
    unfold AffineLinearEval.linearValueFrom
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro offset _
    change toField coefficients[0 + offset]!.bv * toField (left.bv ^^^ right.bv) ^ (2 ^ (0 + offset)) = _
    rw [toField_xor, add_pow_char_pow (p := 2), mul_add]

def KernelSound (map : U64 → U64) (state : EliminationState) : Prop :=
  ∀ i < state.rank.val, map (entry state.kernel i) = 0#u64

private theorem trace_order {columns : Slice U64} {start stop : Nat} {before after : EliminationState}
    (trace : ColumnTrace columns start before stop after) : start ≤ stop := by
  induction trace <;> omega

/-- The native column sweep preserves both the image/preimage graph and
    the zero-image property of every kernel direction written so far. -/
theorem elimination_sound {columns : Slice U64} {start stop : Nat} {before after : EliminationState}
    (trace : ColumnTrace columns start before stop after)
    (map : U64 → U64) (linear : XorLinear map)
    (columnValues : ∀ i < 64, map (basisBit i) = columns[i]!)
    (stopBound : stop ≤ 64) (rankBound : before.rank.val ≤ start)
    (graph : Graph map before.images before.preimages) (kernel : KernelSound map before) :
    Graph map after.images after.preimages ∧ KernelSound map after := by
  induction trace with
  | finished => exact ⟨graph, kernel⟩
  | dependent index state reduced rank path increment stop output rest ih =>
    have indexBound : index < 64 := (trace_order rest).trans stopBound
    have zero := reduce_graph map linear graph path (columnValues index indexBound)
    have writable : state.rank.val < (64#usize).val := by change state.rank.val < 64; omega
    apply ih stopBound (by simp only; omega) graph
    intro i inside
    change i < rank.val at inside
    change map (entry (state.kernel.set state.rank reduced) i) = 0#u64
    by_cases same : i = state.rank.val
    · subst i
      rw [entry_set_same _ _ _ writable]
      exact zero
    · rw [entry_set_other _ _ _ _ (Ne.symm same)]
      exact kernel i (by omega)
  | independent index state reduced final path _ stop output rest ih =>
    have indexBound : index < 64 := (trace_order rest).trans stopBound
    have image := reduce_graph map linear graph path (columnValues index indexBound)
    exact ih stopBound (by simp only; omega) (insert_graph map graph image) kernel

/-- Each successful original GF64 solve returns a particular preimage
    of the constant term and directions in the kernel of the represented
    linearized polynomial. Spanning and independence are separate. -/
theorem native_solve_map_sound {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (bits : field.BITS = .ok 64#u32) (scale : TimesXMod.ExactScaleXor kernels)
    (affine : Slice U64) (initial written : Columns) (base : U64) (rank : Usize)
    (positive : 0 < affine.length) (width : affine.length ≤ 65)
    (normal : solve_map field kernels affine initial = .ok (some (base, rank), written)) :
    ∃ coefficients : Slice U64, coefficients.val = affine.val.drop 1 ∧
      AffineLinearEval.linearValueFrom coefficients base 0 = toField affine[0]!.bv ∧
      ∀ i < rank.val, AffineLinearEval.linearValueFrom coefficients (entry written i) 0 = 0 := by
  obtain ⟨coefficients, table, output, reduced, final, linear, tableOK, trace, _, _, reduction, solved⟩ :=
    solve_map_gf64_refines field kernels bits scale affine initial positive width
  let columns := foldColumns coefficients table 0 (Array.repeat 64#usize 0#u64) coefficients.length
  let map := linearWord coefficients
  have mapLinear : XorLinear map := linear_word_additive coefficients
  have coefficientWidth : coefficients.length ≤ 64 := by
    have length : coefficients.length = affine.length - 1 := by
      rw [Slice.length, linear, List.length_drop]
    omega
  have columnValues (i : Nat) (active : i < 64) : map (basisBit i) = columns.to_slice[i]! := by
    apply U64.bv_eq_imp_eq
    apply toField_injective
    change toField (linearWord coefficients (basisBit i)).bv = toField columns.to_slice[i]!.bv
    rw [linear_word_field, Slice.getElem!_Nat_eq, Array.to_slice, Slice.from_val]
    change AffineLinearEval.linearValueFrom coefficients (column 0 i) 0 = toField (entry columns i).bv
    exact (native_columns_linearized coefficients table tableOK coefficientWidth i active).symm
  have graph : Graph map (initialElimination initial).images (initialElimination initial).preimages := by
    intro i active nonzero
    change entry (Array.repeat 64#usize 0#u64) i ≠ 0#u64 at nonzero
    exact (nonzero (entry_repeat _ _ _ active)).elim
  have kernel : KernelSound map (initialElimination initial) := by
    intro i active
    change i < 0 at active
    omega
  obtain ⟨finalGraph, finalKernel⟩ := elimination_sound trace map mapLinear columnValues
    (Nat.le_refl _) (Nat.zero_le _) graph kernel
  have same := Result.ok_injective (solved.symm.trans normal)
  by_cases zero : final = 0#u64
  · simp only [zero, ite_true] at same
    have pair := Option.some.inj (congrArg Prod.fst same)
    have baseEq : reduced = base := congrArg Prod.fst pair
    have rankEq : output.rank = rank := congrArg Prod.snd pair
    have writtenEq : output.kernel = written := congrArg Prod.snd same
    have value := reduce_target_graph map mapLinear finalGraph reduction
    have mapZero := mapLinear.1
    rw [zero, mapZero] at value
    have image : map reduced = affine[0]! := by
      apply U64.bv_eq_imp_eq
      have exactBits := congrArg UScalar.bv value
      change (map reduced).bv ^^^ (0 : BitVec 64) = (0 : BitVec 64) ^^^ affine[0]!.bv at exactBits
      have left : (map reduced).bv ^^^ (0 : BitVec 64) = (map reduced).bv := BitVec.xor_zero
      have right : (0 : BitVec 64) ^^^ affine[0]!.bv = affine[0]!.bv := BitVec.zero_xor
      exact left.symm.trans (exactBits.trans right)
    refine ⟨coefficients, linear, ?_, ?_⟩
    · rw [← baseEq, ← linear_word_field]
      change toField (map reduced).bv = _
      rw [image]
    · intro i active
      rw [← writtenEq, ← linear_word_field]
      have zero := finalKernel i (by rwa [rankEq])
      change toField (map (entry output.kernel i)).bv = 0
      rw [zero]
      exact toField_zero
  · simp only [zero, ite_false] at same
    have impossible : (none : Option (U64 × Usize)) = some (base, rank) := congrArg Prod.fst same
    cases impossible


end BulksketchBridge.AffineSolveMap
