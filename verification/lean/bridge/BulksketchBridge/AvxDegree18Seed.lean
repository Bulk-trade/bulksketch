import BulksketchBridge.AvxInsertDispatch
import BulksketchBridge.AvxTileChunkSum
import BulksketchBridge.RebuiltLocatorPolynomial

namespace BulksketchBridge.AvxInsertDispatch

open Aeneas.Std AvxInsertDispatchRuntime Algebra.Gf64 RebuiltLfsr AvxTileChunkSum
open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
  (insert_nonzero)

/-- The exact value-frame contract used by the public 18-ID tile route. -/
def Degree18TileWords (tile : Tile) : Prop :=
  ∀ odd ids : Slice U64, odd.length = 18 → ids.length = 18 →
    ∃ output, tile 4#usize false odd ids = .ok output ∧ output.length = odd.length ∧
      ∀ slot, slot < odd.length →
        toField output[slot]!.bv = toField odd[slot]!.bv + (ids.val.map (oddPower slot)).sum

/-- The original public dispatch writes all 18 seed words for distinct
roots once the exact four-vector tile word frame is supplied. -/
def ActualNativeAvxDegree18Seed : Prop :=
  ∀ (one18 one32 : Single) (single : SingleCapacity) (sparse : Batch) (tile : Tile),
    Degree18TileWords tile →
    ∀ shape roots : Slice U64,
      shape.length = 18 → roots.length = 18 → roots.val.Nodup →
      ∃ seed : Slice U64,
        insert_nonzero one18 one32 single sparse tile gf64 (zeroWords shape) roots = .ok seed ∧
        seed.length = shape.length ∧
        ∀ slot, slot < seed.length →
          toField seed[slot]!.bv = Reconciliation.oddSyndrome (rootSupport roots) slot

theorem native_avx_degree18_seed : ActualNativeAvxDegree18Seed := by
  classical
  intro one18 one32 single sparse tile tileLaw shape roots width count distinct
  have zeroLength : (zeroWords shape).length = shape.length := by simp [zeroWords]
  obtain ⟨seed, ran, len, meaning⟩ := tileLaw (zeroWords shape) roots (zeroLength.trans width) count
  have routed := public_degree_18_seed_route one18 one32 single sparse tile
    (zeroWords shape) roots seed (zeroLength.trans width) count ran
  refine ⟨seed, routed, len.trans zeroLength, ?_⟩
  intro slot inSeed
  have inside : slot < shape.length := by rwa [← zeroLength, ← len]
  have zero : (zeroWords shape)[slot]! = 0#u64 := by simp [zeroWords, inside]
  rw [meaning slot (by rwa [len] at inSeed), zero]
  simp only [show (0#u64).bv = 0 from rfl, toField_zero, zero_add]
  have injective : Function.Injective (fun word : U64 => toField word.bv) :=
    fun left right equal => U64.bv_eq_imp_eq left right (toField_injective equal)
  simp only [Reconciliation.oddSyndrome, Reconciliation.powerSum, rootSupport]
  rw [List.sum_toFinset _ (distinct.map injective), List.map_map]
  rfl

#print axioms native_avx_degree18_seed

end BulksketchBridge.AvxInsertDispatch
