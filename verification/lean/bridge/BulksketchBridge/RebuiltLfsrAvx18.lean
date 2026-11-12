import BulksketchBridge.RebuiltLfsrAvx
import BulksketchBridge.AvxDegree18Seed

namespace BulksketchBridge.RebuiltLfsr

open Aeneas.Std AvxSquareRuntime AvxSquare AvxInsertDispatchRuntime
open Algebra.Gf64 Reconciliation DenseCoefficient
open bulksketch.backend.contract bulksketch.backend.portable
open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
  (multiply_linear odd_recurrence_matches insert_nonzero)

set_option maxRecDepth 4096

/-- Exact rebuilt verifier at degree eighteen using the original public AVX
seed dispatch. The tile's per-word theorem supplies its only seed premise. -/
def ActualRebuiltLfsrAvx18WithTileLaw : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
    ∀ (portable : {F : Type} → bulksketch.field.BinaryField F → BulkKernels Portable F)
      (one18 one32 : Single) (single : SingleCapacity) (sparse : Batch) (tile : Tile)
      {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    AvxInsertDispatch.Degree18TileWords tile →
    kernels.multiply_linear = multiply_linear load store portable avxField →
    kernels.odd_recurrence_matches = odd_recurrence_matches load portable avxField →
    kernels.insert_nonzero = insert_nonzero one18 one32 single sparse tile avxField →
    squaringLaw kernels →
    ∀ (roots odd coefficients expected : Slice U64),
      roots.length = 18 → 18 ≤ odd.length → 18 ≤ expected.length → 18 < coefficients.length →
      roots.val.Nodup → (0 : Field) ∉ rootSupport roots →
      ∃ accepted updatedCoefficients updatedExpected,
        bulksketch.decode.verify.rebuilt_lfsr avxField kernels roots odd coefficients expected =
          .ok (accepted, updatedCoefficients, updatedExpected) ∧
        (accepted = true ↔ ∀ i, i < odd.length →
          toField odd[i]!.bv = oddSyndrome (rootSupport roots) i)

theorem rebuilt_lfsr_avx18_with_tile_law : ActualRebuiltLfsrAvx18WithTileLaw := by
  intro load store loadLaw storeLaw portable one18 one32 single sparse tile K kernels tileLaw
    linearEq recurrenceEq insertEq square roots odd coefficients expected count oddRoom seedRoom coeffRoom unique nonzero
  let shape := prefixSlice expected 18
  have shapeWidth : shape.length = 18 := by
    change (prefixSlice expected 18).length = _
    rw [prefix_length, Nat.min_eq_left seedRoom]
  obtain ⟨seed, ran, length, meaning⟩ := AvxInsertDispatch.native_avx_degree18_seed
    one18 one32 single sparse tile tileLaw shape roots shapeWidth count unique
  have length18 : seed.length = 18 := length.trans shapeWidth
  have seedRan : kernels.insert_nonzero (zeroWords (prefixSlice expected seed.length)) roots = .ok seed := by
    rw [insertEq, length18]
    exact ran
  apply rebuilt_lfsr_avx load store loadLaw storeLaw portable kernels linearEq recurrenceEq square
    roots odd coefficients expected seed unique nonzero (by omega)
  · rw [count, Nat.min_eq_left oddRoom]
    exact seedRoom
  · rw [count, Nat.min_eq_left oddRoom]
    exact length18
  · exact seedRan
  · exact meaning

#print axioms rebuilt_lfsr_avx18_with_tile_law

end BulksketchBridge.RebuiltLfsr
