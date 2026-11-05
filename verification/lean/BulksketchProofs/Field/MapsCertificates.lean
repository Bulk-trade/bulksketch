import BulksketchProofs.MapsChallenges

namespace BulksketchProofs.Field.Maps

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
/-- All 4096 source-row/derived-column coefficients are checked by the kernel. -/
theorem columns_match_rows : MapsChallenges.columnsMatchSourceRows := by
  unfold MapsChallenges.columnsMatchSourceRows
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
/-- Every actual table entry, not a sample, equals its independent matrix image. -/
theorem chunk_entries_match : MapsChallenges.allChunkEntriesMatchMatrix := by
  unfold MapsChallenges.allChunkEntriesMatchMatrix
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem chunks_basis_certificate :
    ∀ index : Fin 64, quadraticChunkValue (Period.basisWord index) =
      quadraticValue (Period.basisWord index) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem trace_basis_certificate :
    ∀ index : Fin 64, absoluteTrace (Period.basisWord index) = traceWord (Period.basisWord index) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem right_inverse_basis_certificate :
    ∀ index : Fin 64, quadratic (quadraticValue (Period.basisWord index)) =
      traceProjection (Period.basisWord index) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem left_inverse_basis_certificate :
    ∀ index : Fin 64, quadraticValue (quadratic (Period.basisWord index)) =
      normalizedProjection (Period.basisWord index) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem trace_quadratic_basis_certificate :
    ∀ index : Fin 64, traceWord (quadratic (Period.basisWord index)) = 0 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem normalized_basis_certificate :
    ∀ index : Fin 64, (quadraticValue (Period.basisWord index)) &&& 1 = 0 := by
  decide +kernel

end BulksketchProofs.Field.Maps
