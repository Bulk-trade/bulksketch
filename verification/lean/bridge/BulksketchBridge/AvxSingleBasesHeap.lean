import BulksketchBridge.AvxSingleBasesField

namespace BulksketchBridge.AvxSingleBases

open Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxSquareRuntime
open AvxSquare X86MaskedMemory X86MaskedMemory.Allocation X86MaskedMemory.Llbc Algebra.Gf64
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Charon's x86_64 layout places the nine 64-row tables first, then the
two 32-row tables at byte 36864. Every row occupies 64 bytes. -/
def layoutRow (table : InsertionBases) (row : Nat) : Row :=
  if row < 576 then sixRow table (row / 64) (row % 64)
  else fiveRow table ((row - 576) / 32) ((row - 576) % 32)

def layoutWord (table : InsertionBases) (index : Nat) : BitVec 64 :=
  (layoutRow table (index / 8)).val[index % 8]!.bv

private theorem layout_six (table : InsertionBases) (chunk index : Nat)
    (chunkBound : chunk < 9) (indexBound : index < 64) :
    layoutRow table (64 * chunk + index) = sixRow table chunk index := by
  unfold layoutRow
  rw [ite_eq_left (by omega : 64 * chunk + index < 576),
    show (64 * chunk + index) / 64 = chunk by omega,
    show (64 * chunk + index) % 64 = index by omega]

private theorem layout_five (table : InsertionBases) (chunk index : Nat)
    (chunkBound : chunk < 2) (indexBound : index < 32) :
    layoutRow table (576 + 32 * chunk + index) = fiveRow table chunk index := by
  unfold layoutRow
  rw [ite_eq_right (by omega : ¬576 + 32 * chunk + index < 576),
    show (576 + 32 * chunk + index - 576) / 32 = chunk by omega,
    show (576 + 32 * chunk + index - 576) % 32 = index by omega]

/-- An admitted initialized table allocation with the captured row layout. -/
structure HeapTable (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
    (base : Address) (table : InsertionBases) : Prop where
  view : ReadView live la57 heap base 40960 64
  values : FiniteWordWindow heap base 5120 (layoutWord table)

def RowLoad (heap : AddressHeap) (permit : Address → Bool) (base : Address)
    (row : Nat) (words : Row) : Prop :=
  let address := base + BitVec.ofNat 64 (64 * row)
  exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨address.toNat, words.to_slice.len⟩) =
    some (.register (loadWords words.to_slice), liftHeap heap)

theorem allocated_row (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
    (base : Address) (permit : Address → Bool) (table : InsertionBases)
    (admitted : HeapTable live la57 heap base table) (row : Nat) (room : row < 640) :
    RowLoad heap permit base row (layoutRow table row) := by
  let words := (layoutRow table row).to_slice
  let address := base + BitVec.ofNat 64 (64 * row)
  have length : words.length = 8 := by
    simp only [words, Slice.length, Array.val_to_slice, Array.property]
    rfl
  have byteView : ReadView live la57 heap base (8 * 5120) 8 := by
    refine ⟨admitted.view.nonnull, ?_, admitted.view.allocated, admitted.view.initialized⟩
    have aligned := admitted.view.aligned
    omega
  have view : ReadView live la57 heap address (8 * words.length) 8 := by
    rw [length]
    have window := read_word_window byteView (8 * row) 8 (by decide) (by omega)
    simpa only [address, show 8 * (8 * row) = 64 * row by omega] using window
  have values : FiniteWordWindow heap address words.length (fun i => words[i]!.bv) := by
    intro i active byte
    have iRoom : i < 8 := by rwa [length] at active
    have byteRoom := byte.isLt
    have fits := admitted.view.no_wrap
    have oldAddress : address.toNat = base.toNat + 64 * row :=
      address_add_exact base (64 * row) (by omega)
    have exactAddress : address + BitVec.ofNat 64 (8 * i + byte.val) =
        base + BitVec.ofNat 64 (8 * (8 * row + i) + byte.val) := by
      apply BitVec.eq_of_toNat_eq
      rw [address_add_exact _ _ (by rw [oldAddress]; omega), oldAddress, address_add_exact _ _ (by omega)]
      omega
    rw [exactAddress, admitted.values (8 * row + i) (by omega) byte]
    have read : layoutWord table (8 * row + i) = words[i]!.bv := by
      simp only [layoutWord, show (8 * row + i) / 8 = row by omega, show (8 * row + i) % 8 = i by omega,
        words, Slice.getElem!_Nat_eq, Array.val_to_slice]
    rw [read]
  exact square_load_allocated live la57 heap address words permit (by rw [length]) view values

/-- The eleven original calls read complete aligned rows and leave the static
heap unchanged. This retains the six-bit/five-bit address decomposition. -/
structure AllocatedReads (heap : AddressHeap) (permit : Address → Bool) (base : Address)
    (table : InsertionBases) (id : U64) : Prop where
  six : ∀ chunk : Fin 9,
    let index := (sixIndex id (6 * chunk.val)).val
    RowLoad heap permit base (64 * chunk.val + index) (sixRow table chunk.val index)
  firstFive :
    let index := (fiveIndex id 54).val
    RowLoad heap permit base (576 + index) (fiveRow table 0 index)
  lastFive :
    let index := (lastIndex id).val
    RowLoad heap permit base (608 + index) (fiveRow table 1 index)

theorem allocated_reads (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
    (base : Address) (permit : Address → Bool) (table : InsertionBases)
    (admitted : HeapTable live la57 heap base table) (id : U64) :
    AllocatedReads heap permit base table id := by
  refine ⟨?_, ?_, ?_⟩
  · intro chunk
    let index := (sixIndex id (6 * chunk.val)).val
    have chunkBound := chunk.isLt
    have indexBound : index < 64 := by unfold index; rw [six_index_exact]; exact Nat.mod_lt _ (by decide)
    have read := allocated_row live la57 heap base permit table admitted (64 * chunk.val + index) (by omega)
    rwa [layout_six table chunk.val index chunkBound indexBound] at read
  · let index := (fiveIndex id 54).val
    have indexBound : index < 32 := by unfold index; rw [five_index_exact]; exact Nat.mod_lt _ (by decide)
    have read := allocated_row live la57 heap base permit table admitted (576 + 32 * 0 + index) (by omega)
    rwa [layout_five table 0 index (by decide) indexBound] at read
  · let index := (lastIndex id).val
    have indexBound : index < 32 := (last_index_exact id).2
    have read := allocated_row live la57 heap base permit table admitted (576 + 32 * 1 + index) (by omega)
    rwa [layout_five table 1 index (by decide) indexBound] at read

/-- Original source lookup, physical read windows, and the encoder's lane
premise under the specified static values and live allocation. -/
def ActualAllocatedSingleBases : Prop :=
  ∀ (tableModel : Result InsertionBases) (loadModel : Load), LoadLaw loadModel →
  ∀ table, tableModel = .ok table → TableLaw table →
  ∀ (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap) (base : Address) (permit : Address → Bool),
    HeapTable live la57 heap base table →
    ∀ id : U64, ∃ output, single_bases tableModel loadModel id = .ok output ∧
      (∀ lane : Fin 8, toField (flatten output lane) = laneFrobenius lane id.bv) ∧
      AllocatedReads heap permit base table id

theorem allocated_single_bases_refines : ActualAllocatedSingleBases := by
  intro tableModel loadModel law table lookup valid live la57 heap base permit admitted id
  exact ⟨expected table id, single_bases_refines tableModel loadModel law table lookup id,
    expected_lanes table valid id, allocated_reads live la57 heap base permit table admitted id⟩

end BulksketchBridge.AvxSingleBases
