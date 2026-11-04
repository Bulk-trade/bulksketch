import BulksketchProofs.Field.PeriodSpec

/-! Finite polynomial-basis certificate. `decide +kernel` asks Lean's original
kernel to reduce the concrete 64 basis images; no native-evaluation axiom is
used and no universal input word is enumerated. -/

namespace BulksketchProofs.Field.Period

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem basis_certificate : BasisCertificate := by
  unfold BasisCertificate
  decide +kernel

end BulksketchProofs.Field.Period
