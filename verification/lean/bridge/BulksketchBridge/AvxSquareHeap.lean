import BulksketchBridge.AvxSquareScalarMemory
import BulksketchBridge.DenseMul

namespace BulksketchBridge.AvxSquare

open Aeneas.Std Aeneas.Std.AvxSquareRuntime X86MaskedMemory X86MaskedMemory.Allocation
open scoped BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096

private theorem seed_frame_byte {before after : AddressHeap} {dst scratch src : Address} {dw sw read : Nat}
    (frame : SeedFrame before after dst scratch dw sw)
    (apartDst : Disjoint dst (8 * dw) src read) (apartScratch : Disjoint scratch (8 * (2 * sw)) src read)
    (fits : src.toNat + read ≤ 2 ^ 64) (offset : Nat) (inside : offset < read) :
    after (src + BitVec.ofNat 64 offset) = before (src + BitVec.ofNat 64 offset) :=
  frame _ (disjoint_outside apartDst fits offset inside) (disjoint_outside apartScratch fits offset inside)

private theorem seed_frame_read {live la57 before after dst scratch src dw sw read alignment}
    (frame : SeedFrame before after dst scratch dw sw)
    (apartDst : Disjoint dst (8 * dw) src read) (apartScratch : Disjoint scratch (8 * (2 * sw)) src read)
    (view : ReadView live la57 before src read alignment) :
    ReadView live la57 after src read alignment := by
  refine ⟨view.nonnull, view.aligned, view.allocated, ?_⟩
  intro offset inside
  rw [seed_frame_byte frame apartDst apartScratch view.no_wrap offset inside]
  exact view.initialized offset inside

private theorem seed_frame_words {before after dst scratch src dw sw count words}
    (frame : SeedFrame before after dst scratch dw sw)
    (apartDst : Disjoint dst (8 * dw) src (8 * count)) (apartScratch : Disjoint scratch (8 * (2 * sw)) src (8 * count))
    (fits : src.toNat + 8 * count ≤ 2 ^ 64) (bytes : FiniteWordWindow before src count words) :
    FiniteWordWindow after src count words := by
  intro index active byte
  rw [seed_frame_byte frame apartDst apartScratch fits _ (by have := byte.isLt; omega)]
  exact bytes index active byte

/-- Compose the original typed square body with the exact scalar byte
effects of fill and seed and the original masked load/store LLBC of the
vector phase. The scalar model takes the captured RawProduct layout as
a heap view. Allocation provenance and compiler-to-ISA correctness
remain separate premises and obligations. -/
def ActualAllocatedAvxSquare : Prop :=
  ∀ (loadModel : Load) (storeModel : Store), LoadLaw loadModel → StoreLaw storeModel →
    ∀ (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap) (permit : Address → Bool)
      (inputBase tableBase dstBase scratchBase : Address)
      (input table dst : Slice U64) (scratch : Slice Raw),
      input.length ≤ dst.length → input.length ≤ scratch.length →
      dst.length + 8 ≤ Usize.max → dst.length / 2 * dst.length ≤ table.length →
      SeedViews live la57 heap permit inputBase dstBase scratchBase input dst scratch →
      SeedDisjoint inputBase dstBase scratchBase input.length dst.length scratch.length →
      ReadView live la57 heap tableBase (8 * table.length) 8 →
      FiniteWordWindow heap tableBase table.length (fun i => table[i]!.bv) →
      Disjoint dstBase (8 * dst.length) tableBase (8 * table.length) →
      Disjoint scratchBase (8 * (2 * scratch.length)) tableBase (8 * table.length) →
      let degree := dst.length
      let first := (degree + 1) / 2
      let zeros := RebuiltLfsr.zeroWords dst
      let seeded := seed input 0 first zeros scratch input.length
      let final := squareResult input table dst scratch
      ∃ fillHeap seedHeap finalHeap : AddressHeap,
        bulksketch.backend.x86_vpclmul512.square_mod loadModel storeModel input table dst scratch = .ok final ∧
        FillTrace dstBase permit 0 degree heap fillHeap ∧
        SeedTrace inputBase dstBase scratchBase permit input first 0 input.length zeros scratch fillHeap
          seeded.1 seeded.2 seedHeap ∧
        BlockTrace (DenseMul.takeSlice seeded.2 input.length) table degree first tableBase dstBase permit 0
          seeded.1 seedHeap final.1 finalHeap ∧
        SeedViews live la57 finalHeap permit inputBase dstBase scratchBase input final.1 final.2 ∧
        ReadView live la57 finalHeap tableBase (8 * table.length) 8 ∧
        FiniteWordWindow finalHeap tableBase table.length (fun i => table[i]!.bv) ∧
        SeedFrame heap finalHeap dstBase scratchBase degree scratch.length

theorem allocated_square_refines : ActualAllocatedAvxSquare := by
  intro loadModel storeModel loadLaw storeLaw live la57 heap permit inputBase tableBase dstBase scratchBase
    input table dst scratch inputBound scratchBound safe tableBound views apart tableView tableBytes apartDst apartScratch
  let degree := dst.length
  let first := (degree + 1) / 2
  let zeros := RebuiltLfsr.zeroWords dst
  let seeded := seed input 0 first zeros scratch input.length
  let final := squareResult input table dst scratch
  have zeroLen : zeros.length = degree := by simp [zeros, RebuiltLfsr.zeroWords, Slice.length, degree]
  obtain ⟨fillHeap, fill, fillBytes, fillView, fillFrame⟩ :=
    fill_trace live la57 heap dstBase permit (fun i => dst[i]!.bv) degree 0 degree
      (by omega) views.dstView views.dstBytes
  have zeroBytes : FiniteWordWindow fillHeap dstBase degree (fun i => zeros[i]!.bv) := by
    intro i active byte
    have read := fillBytes i active byte
    have inFill : 0 ≤ i ∧ i < 0 + degree := by omega
    simp only [ite_eq_left inFill] at read
    have value : zeros[i]! = 0#u64 := by
      simp only [zeros, RebuiltLfsr.zeroWords, Slice.getElem!_Nat_eq, Slice.from_val]
      exact List.getElem!_replicate _ active
    simpa only [value, show (0#u64 : U64).bv = 0 from rfl] using read
  have filledViews : SeedViews live la57 fillHeap permit inputBase dstBase scratchBase input zeros scratch := by
    refine ⟨frame_read_view fillFrame apart.dstInput views.inputView,
      frame_word_view fillFrame apart.dstInput views.inputView.no_wrap views.inputBytes, ?_, ?_,
      frame_write_view fillFrame (Disjoint.flip apart.scratchDst) views.scratchView,
      frame_word_view fillFrame (Disjoint.flip apart.scratchDst) views.scratchView.toReadView.no_wrap views.scratchBytes⟩
    · rwa [zeroLen]
    · rwa [zeroLen]
  obtain ⟨seedHeap, seededTrace, seededViews, seedFrame⟩ :=
    seed_trace live la57 fillHeap permit inputBase dstBase scratchBase input zeros scratch
      0 first input.length (by omega) scratchBound (by rw [zeroLen]) filledViews (by rwa [zeroLen])
  rw [zeroLen] at seedFrame
  have filledTableView := frame_read_view fillFrame apartDst tableView
  have filledTableBytes := frame_word_view fillFrame apartDst tableView.no_wrap tableBytes
  have seedTableView := seed_frame_read seedFrame apartDst apartScratch filledTableView
  have seedTableBytes := seed_frame_words seedFrame apartDst apartScratch filledTableView.no_wrap filledTableBytes
  have seededDst : seeded.1.length = degree := (seed_dst_length ..).trans zeroLen
  have seededRaw : seeded.2.length = scratch.length := seed_scratch_length ..
  let activeRaw := DenseMul.takeSlice seeded.2 input.length
  have activeBound : activeRaw.length ≤ degree := by
    rw [show activeRaw.length = min input.length seeded.2.length from DenseMul.take_length ..]
    exact (Nat.min_le_left _ _).trans inputBound
  have seedDstView : WriteView live la57 seedHeap permit dstBase (8 * seeded.1.length) 8 := seededViews.dstView
  have seedDstBytes : FiniteWordWindow seedHeap dstBase seeded.1.length (fun i => seeded.1[i]!.bv) :=
    seededViews.dstBytes
  rw [seededDst] at seedDstView seedDstBytes
  obtain ⟨finalHeap, blocks, finalBytes, finalView, finalTableView, finalTableBytes, blockFrame⟩ :=
    allocated_block_scan live la57 tableBase dstBase table activeRaw permit degree degree 0 seedHeap seeded.1
      seededDst (by omega) activeBound tableBound seedTableView seedDstView seedTableBytes seedDstBytes apartDst
  have finalDst : final.1.length = degree := (square_result_lengths input table dst scratch).1
  have finalRaw : final.2 = seeded.2 := rfl
  have finalView' : SeedViews live la57 finalHeap permit inputBase dstBase scratchBase input final.1 final.2 := by
    refine ⟨frame_read_view blockFrame apart.dstInput seededViews.inputView,
      frame_word_view blockFrame apart.dstInput seededViews.inputView.no_wrap seededViews.inputBytes, ?_, ?_, ?_, ?_⟩
    · rwa [finalDst]
    · rw [finalDst]
      exact finalBytes
    · rw [finalRaw]
      exact frame_write_view blockFrame (by rw [seededRaw]; exact Disjoint.flip apart.scratchDst) seededViews.scratchView
    · rw [finalRaw]
      exact frame_word_view blockFrame (by rw [seededRaw]; exact Disjoint.flip apart.scratchDst)
        seededViews.scratchView.toReadView.no_wrap seededViews.scratchBytes
  refine ⟨fillHeap, seedHeap, finalHeap, square_mod_refines loadModel storeModel loadLaw storeLaw
    input table dst scratch inputBound scratchBound safe tableBound, fill, seededTrace, blocks, finalView',
    finalTableView, finalTableBytes, ?_⟩
  intro address outsideDst outsideScratch
  exact (blockFrame address outsideDst).trans ((seedFrame address outsideDst outsideScratch).trans
    (fillFrame address outsideDst))

end BulksketchBridge.AvxSquare
