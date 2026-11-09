import BulksketchBridge.AvxEncodeEntry
import BulksketchBridge.AvxEncodeInsert
import BulksketchBridge.DegreeProbeRuntimeEncoding
import BulksketchBridge.AvxInsertionBasesStatic
import BulksketchBridge.ConcreteRebuiltDictionaries

namespace BulksketchBridge.AvxEncodeEntry

open Aeneas Aeneas.Std Algebra.Gf64 DenseCoefficient RebuiltLfsr
open AvxInsertDispatchRuntime AvxSquareRuntime AvxSquare AvxInsertDispatch
open bulksketch.backend.contract
open bulksketch.backend.x86_vpclmul512
open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels (encode_nonzero)
open BulksketchBridge.DegreeProbeRuntime (encodedWords CorrectEncoding encodedWords_slot encodedWords_length)

set_option maxRecDepth 4096
set_option maxHeartbeats 1300000

private theorem encodeValue_sum (ids : Slice U64) (slot : Nat) (small : ids.length = 1 ∨ ids.length = 2) :
    AvxEncode18.encodeValue ids slot = (ids.val.map (AvxTileChunkSum.oddPower slot)).sum := by
  rcases small with one | two
  · have width : ids.val.length = 1 := one
    obtain ⟨word, words⟩ := List.length_eq_one_iff.mp width
    simp [AvxEncode18.encodeValue, words, Slice.getElem!_Nat_eq, AvxTileChunkSum.oddPower]
  · have width : ids.val.length = 2 := two
    cases contents : ids.val with
    | nil => simp [contents] at width
    | cons a rest =>
      cases rest with
      | nil => simp [contents] at width
      | cons b rest =>
        have length : (a :: b :: rest).length = 2 := by simpa only [contents] using width
        have empty : rest = [] := List.length_eq_zero_iff.mp (by
          simp only [List.length_cons] at length
          omega)
        simp [AvxEncode18.encodeValue, contents, empty, Slice.getElem!_Nat_eq, AvxTileChunkSum.oddPower]

private theorem slice_of_field_slots {left right : Slice U64}
    (length : left.length = right.length)
    (slots : ∀ slot < left.length, toField left[slot]!.bv = toField right[slot]!.bv) : left = right := by
  apply Slice.ext_getElem length
  intro slot inside insideRight
  rw [Slice.Inhabited_getElem_eq_getElem! left slot inside,
    Slice.Inhabited_getElem_eq_getElem! right slot insideRight]
  exact U64.bv_eq_imp_eq _ _ (toField_injective (slots slot inside))

private theorem encode_fast_words (load : Load) (store : Store) (loadLaw : LoadLaw load)
    (storeLaw : StoreLaw store) (odd ids : Slice U64) (shape : odd.length = 18)
    (small : ids.length = 1 ∨ ids.length = 2) :
    encode_18 (single_bases INSERT_BASES load) store odd ids = .ok (encodedWords odd ids) := by
  obtain ⟨written, normal, width, lanes, _⟩ :=
    AvxInsertionBases.static_encode_refines load store loadLaw storeLaw odd ids (by omega) small
  rw [normal]
  congr 1
  apply slice_of_field_slots (width.trans (encodedWords_length odd ids).symm)
  intro slot inside
  have row : slot < odd.length := by omega
  rw [encodedWords_slot odd ids slot row, PortableEncoding.foldColumn_field]
  change toField written[slot]!.bv =
    toField (0 : BitVec 64) + (ids.val.map (AvxTileChunkSum.oddPower slot)).sum
  rw [toField_zero, zero_add]
  exact (lanes ⟨slot, by omega⟩).trans (encodeValue_sum ids slot small)

private theorem insertion_matches_portable (load : Load) (store : Store) (loadLaw : LoadLaw load)
    (storeLaw : StoreLaw store) (one32 : Single) (law32 : SingleLaw one32 32)
    (single : SingleCapacity) (law72 : SingleLaw (single 72#usize) 72)
    (law89 : SingleLaw (single 89#usize) 89) (odd ids : Slice U64) :
    nativeInsert load store one32 single gf64 odd ids =
      (RebuiltLfsr.portableKernels).insert_nonzero odd ids := by
  obtain ⟨native, nativeRun, nativeLength, nativeSlots⟩ :=
    avx_insert_all_routes load store loadLaw storeLaw one32 law32 single law72 law89 odd ids
  obtain ⟨portable, portableRun, portableLength, portableSlots⟩ :=
    PortableEncoding.insert_nonzero_refines odd ids
  change nativeInsert load store one32 single gf64 odd ids =
    bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
      gf64 odd ids
  rw [nativeRun, portableRun]
  congr 1
  apply slice_of_field_slots (nativeLength.trans portableLength.symm)
  intro slot inside
  have row : slot < odd.length := by omega
  rw [nativeSlots slot row, portableSlots slot row, PortableEncoding.foldColumn_field]
  rfl

def nativeEncode (load : Load) (store : Store) (one32 : Single)
    (single : SingleCapacity) : Batch :=
  encode_nonzero (encode_18 (single_bases INSERT_BASES load) store)
    (nativeInsert load store one32 single) gf64

/-- Every route in the original AVX encoder produces the exact word frame.
The concrete register and slice laws are explicit. The three specialized
singleton endpoints can be supplied independently. -/
def ActualNativeAvxEncoding : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
    ∀ (one32 : Single), SingleLaw one32 32 →
    ∀ (single : SingleCapacity), SingleLaw (single 72#usize) 72 → SingleLaw (single 89#usize) 89 →
    ∀ odd ids, nativeEncode load store one32 single odd ids = .ok (encodedWords odd ids)

theorem native_avx_encoding : ActualNativeAvxEncoding := by
  intro load store loadLaw storeLaw one32 law32 single law72 law89 odd ids
  have matched : nativeInsert load store one32 single gf64 = RebuiltLfsr.portableKernels.insert_nonzero :=
    funext fun odd => funext fun ids =>
      insertion_matches_portable load store loadLaw storeLaw one32 law32 single law72 law89 odd ids
  rw [nativeEncode, avx_encode_entry _ _ gf64 RebuiltLfsr.portableKernels matched]
  have bits : bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS = 64#u32 := by
    simp [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS]
  simp only [expected, bind_ok, bits, eq_self, true_and]
  by_cases fast : odd.length = 18 ∧ (ids.length = 1 ∨ ids.length = 2)
  · rw [ite_eq_left fast]
    exact encode_fast_words load store loadLaw storeLaw odd ids fast.1 fast.2
  · rw [ite_eq_right fast]
    exact DegreeProbeRuntime.encoding_of_portable_default RebuiltLfsr.portableKernels
      rfl (fun _ _ => rfl) odd ids

#print axioms native_avx_encoding

end BulksketchBridge.AvxEncodeEntry
