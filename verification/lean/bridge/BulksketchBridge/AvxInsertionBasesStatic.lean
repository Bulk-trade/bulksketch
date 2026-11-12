import BulksketchBridge.AvxInsertionBasesTableLaw
import Arithmetic.AvxInsertionBasesStaticGenerated
import BulksketchBridge.AvxEncode18Heap
import BulksketchBridge.AvxSingleBasesHeap

namespace BulksketchBridge.AvxInsertionBases

open Aeneas.Std Aeneas.Std.AvxSquareRuntime
open AvxSquare Algebra.Gf64
open bulksketch.backend.x86_vpclmul512

def ActualInsertionBasesStatic : Prop := INSERT_BASES = Result.ok generatedTable

theorem insertion_static_refines : ActualInsertionBasesStatic := by
  unfold ActualInsertionBasesStatic
  rw [INSERT_BASES]
  exact insertion_bases_refines

theorem static_supplies_bases (loadModel : Load) (loadLaw : LoadLaw loadModel) :
    AvxEncode18.BasesLaw (single_bases INSERT_BASES loadModel) :=
  AvxSingleBases.original_bases_law _ loadModel loadLaw generatedTable insertion_static_refines generated_table_law

/-- The exact original encoder receives its actual static lookup, with no
independent Frobenius table premise. -/
def ActualStaticEncode18 : Prop :=
  ∀ (loadModel : Load) (storeModel : Store), LoadLaw loadModel → StoreLaw storeModel →
    ∀ (odd ids : Slice U64), 18 ≤ odd.length → (ids.length = 1 ∨ ids.length = 2) →
      ∃ output,
        encode_18 (single_bases INSERT_BASES loadModel) storeModel odd ids = .ok output ∧
        output.length = odd.length ∧
        (∀ i : Fin 18, toField output[i.val]!.bv = AvxEncode18.encodeValue ids i.val) ∧
        (∀ i : Nat, 18 ≤ i → output[i]! = odd[i]!)

theorem static_encode_refines : ActualStaticEncode18 := by
  intro loadModel storeModel loadLaw storeLaw
  exact AvxEncode18.encode_refines _ storeModel (static_supplies_bases loadModel loadLaw) storeLaw

open X86MaskedMemory X86MaskedMemory.Allocation

/-- The actual static values supply each original table read. The three
output stores leave the separate table allocation and all bytes outside
the 18-word destination prefix unchanged. -/
def ActualAllocatedStaticEncode18 : Prop :=
  ∀ (loadModel : Load) (storeModel : Store), LoadLaw loadModel → StoreLaw storeModel →
    ∀ (live : LiveAllocations) (la57 : Bool) (tableBase outBase : Address)
      (permit : Address → Bool) (odd ids : Slice U64) (heap : AddressHeap) (room : 18 ≤ odd.length),
      (ids.length = 1 ∨ ids.length = 2) →
      AvxSingleBases.HeapTable live la57 heap tableBase generatedTable →
      Disjoint outBase (8 * 18) tableBase 40960 →
      WriteView live la57 heap permit outBase (8 * odd.length) 8 →
      FiniteWordWindow heap outBase odd.length (fun i => odd[i]!.bv) →
      ∃ values : AvxEncode18.Triple, ∃ low high final : AddressHeap,
        encode_18 (single_bases INSERT_BASES loadModel) storeModel odd ids =
          .ok (odd.setSlice! 0 (AvxEncode18.rowPayload odd values room)) ∧
        (∀ i, i < ids.length → AvxSingleBases.AllocatedReads heap permit tableBase generatedTable ids[i]!) ∧
        AvxEncode18.BlockStore outBase permit odd values.1 0 8 heap low ∧
        AvxEncode18.BlockStore outBase permit (AvxEncode18.writeLow odd values) values.2.1 8 16 low high ∧
        AvxEncode18.BlockStore outBase permit (AvxEncode18.writeHigh odd values) values.2.2 16 18 high final ∧
        FiniteWordWindow final outBase odd.length
          (fun i => (odd.setSlice! 0 (AvxEncode18.rowPayload odd values room))[i]!.bv) ∧
        WriteView live la57 final permit outBase (8 * odd.length) 8 ∧
        AvxSingleBases.HeapTable live la57 final tableBase generatedTable ∧
        FramesOutside heap final outBase (8 * 18)

theorem allocated_static_encode_refines : ActualAllocatedStaticEncode18 := by
  intro loadModel storeModel loadLaw storeLaw live la57 tableBase outBase permit odd ids heap
    room admitted table apart outView outBytes
  obtain ⟨values, low, high, final, ran, first, second, third, bytes, finalView, frame⟩ :=
    AvxEncode18.allocated_encode_refines _ storeModel (static_supplies_bases loadModel loadLaw)
      storeLaw live la57 outBase permit odd ids heap room admitted outView outBytes
  have preserved : AvxSingleBases.HeapTable live la57 final tableBase generatedTable :=
    ⟨frame_read_view frame apart table.view,
      frame_word_view frame apart table.view.no_wrap table.values⟩
  exact ⟨values, low, high, final, ran,
    fun i _ => AvxSingleBases.allocated_reads live la57 heap tableBase permit generatedTable table ids[i]!,
    first, second, third, bytes, finalView, preserved, frame⟩

end BulksketchBridge.AvxInsertionBases
