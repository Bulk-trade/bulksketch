import BulksketchBridge.AffineSolveMapColumns
import BulksketchBridge.AffineSolveMapGraph

namespace BulksketchBridge.AffineSolveMap

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.decode.affine bulksketch.backend.contract
open AffineSubspaces (iteratorAt)
open DenseCoefficient (prefixSlice)
open RebuiltLfsr (shared_prefix_normal)

set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

def initialElimination (kernel : Columns) : EliminationState :=
  ⟨kernel, Array.repeat 64#usize 0#u64, Array.repeat 64#usize 0#u64, 0#usize⟩

/-- Exact operational GF64 result, including the retained kernel frame and
the witness path from the constant term to zero or the first vacant pivot. -/
def ActualSolveMapGf64 : Prop :=
  ∀ {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64),
    field.BITS = .ok 64#u32 → TimesXMod.ExactScaleXor kernels →
    ∀ (affine : Slice U64) (kernel : Columns),
      0 < affine.length → affine.length ≤ 65 →
      ∃ (linear : Slice U64) (table : Rows) (output : EliminationState) (reduced final : U64),
        linear.val = affine.val.drop 1 ∧ TablePrefix table 64 ∧
        ColumnTrace
          (foldColumns linear table 0 (Array.repeat 64#usize 0#u64) linear.length).to_slice
          0 (initialElimination kernel) 64 output ∧
        Pivots output.images ∧ output.rank.val ≤ 64 ∧
        Reduced output.images output.preimages 0#u64 affine[0]! reduced final ∧
        solve_map field kernels affine kernel =
          .ok (if final = 0#u64 then some (reduced, output.rank) else none, output.kernel)

theorem solve_map_gf64_refines : ActualSolveMapGf64 := by
  intro K field kernels bits scale affine kernel positive maxLength
  have oneFits : (1#usize).val ≤ affine.length := by change 1 ≤ affine.length; omega
  obtain ⟨linear, suffix, linearValue, linearLength⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec ⟨1#usize⟩ affine oneFits)
  change linear.val = affine.val.drop 1 at linearValue
  change linear.length = affine.length - 1 at linearLength
  have width : linear.length ≤ 64 := by omega
  obtain ⟨table, tableNormal, canonical⟩ := native_table_refines
  let zero : Columns := Array.repeat 64#usize 0#u64
  let columns := foldColumns linear table 0 zero linear.length
  have folds : solve_map_loop0 field kernels 64#u32 (iteratorAt linear 0#usize) 64#usize zero =
      .ok columns := by
    have run := gf64_columns field kernels scale table tableNormal linear 0#usize zero width (by
      change 0 ≤ linear.length
      exact Nat.zero_le _)
    simpa only [show (0#usize).val = 0 from rfl, Nat.sub_zero] using run
  have colLength : columns.to_slice.length = 64 := by
    rw [Array.length_to_slice]
    rfl
  have wholeSlice :
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice U64)) columns { «end» := 64#usize } =
      .ok columns.to_slice := by
    rw [Array.index_SliceIndexRangeToUsizeSlice,
      shared_prefix_normal columns.to_slice 64#usize (by rw [colLength]; decide)]
    apply congrArg Result.ok
    apply Slice.ext
    have len : columns.to_slice.val.length = 64 := colLength
    have all : columns.to_slice.val.length ≤ (64#usize).val := by
      change columns.to_slice.val.length ≤ 64
      omega
    simp only [prefixSlice, Slice.from_val, List.take_of_length_le all]
  let initial := initialElimination kernel
  obtain ⟨output, eliminated, trace, rankBound, pivotInvariant⟩ :=
    eliminate_columns columns.to_slice 0#usize initial (by rw [colLength]) (by change 0 ≤ _; omega)
      (by rfl) empty_pivots
  have readTarget : Slice.index_usize affine 0#usize = .ok affine[0]! := by
    obtain ⟨target, normal, exactValue⟩ := RawMulTable.normal_of_spec _ _
      (Slice.index_usize_spec affine 0#usize (by exact positive))
    rw [normal, exactValue, Slice.getElem!_Nat_eq]
    exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ positive)
  obtain ⟨reduced, final, _, path, _⟩ :=
    eliminate_column output.images output.preimages 0#u64 affine[0]! pivotInvariant
  have target := reduce_target output.images output.preimages output.rank 0#u64 affine[0]! reduced final path
  rw [colLength] at trace rankBound
  refine ⟨linear, table, output, reduced, final, linearValue, canonical, trace, pivotInvariant, rankBound, path, ?_⟩
  have castBits : UScalar.cast .Usize (64#u32) = 64#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.cast_val_eq]
    change 64 % 2 ^ System.Platform.numBits = 64
    have platform := System.Platform.numBits_eq
    rcases platform with width | width <;> rw [width] <;> rfl
  have sliced :
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U64)
        affine { start := 1#usize } = .ok linear := suffix
  have initEnum (words : Slice U64) :
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.U64) ⟨words, 0⟩ =
          .ok (iteratorAt words 0#usize) := rfl
  have foldExact :
      solve_map_loop0 field kernels 64#u32 (iteratorAt linear 0#usize) 64#usize
        (Array.repeat 64#usize 0#u64) = .ok columns := folds
  dsimp only [initial, initialElimination, EliminationState.result] at eliminated
  simp only [solve_map, bits, bind_ok, castBits, lift, sliced, core.slice.Slice.iter,
    initEnum, foldExact, wholeSlice, eliminated]
  dsimp! only
  simp only [readTarget, bind_ok, target]

#print axioms solve_map_gf64_refines

end BulksketchBridge.AffineSolveMap
