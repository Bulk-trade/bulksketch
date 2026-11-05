import BulksketchBridge.MapsQuadraticChallenges

/-!
Kernel linkage of all actual generated native table values and the original
quadratic_rows selector. No table entry or application branch is replaced.
-/

namespace BulksketchBridge.MapsTables

open Aeneas Aeneas.Std

/-- Every64 row literal matches the independently extracted source data exactly. -/
theorem rows_match_source : MapsQuadraticChallenges.allGeneratedRowsMatchSourceData := by
  unfold MapsQuadraticChallenges.allGeneratedRowsMatchSourceData
  simp only [bulksketch.field.maps.GF64_QUADRATIC, Array.make_val,
    BulksketchProofs.Field.Maps.rows,
    BulksketchProofs.Generated.FieldTables.quadraticRows]
  rfl

/-- Every256 table entry, in its original16-by16 order, matches the source data. -/
theorem chunks_match_source : MapsQuadraticChallenges.allGeneratedChunksMatchSourceData := by
  unfold MapsQuadraticChallenges.allGeneratedChunksMatchSourceData
  simp only [bulksketch.field.quadratic_chunks.GF64_QUADRATIC_CHUNKS, Array.make_val,
    BulksketchProofs.Field.Maps.chunks,
    BulksketchProofs.Generated.FieldTables.quadraticChunks]
  rfl

/-- The actual native row selector returns the full64-entry slice normally. -/
theorem quadratic_rows_refines : MapsQuadraticChallenges.actualRowsReturnExactSourceData := by
  refine ⟨Array.to_slice bulksketch.field.maps.GF64_QUADRATIC, ?_, ?_, ?_⟩
  · simp only [bulksketch.field.maps.quadratic_rows,
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS, bind_ok]
    rfl
  · simp only [Array.to_slice, Slice.from_val]
    exact rows_match_source
  · simp only [Array.to_slice, Slice.from_val, Array.property]
    rfl

end BulksketchBridge.MapsTables
