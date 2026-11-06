import BulksketchBridge.PortableInverseChallenges
import BulksketchBridge.InverseUsing

namespace BulksketchBridge.PortableInverse

/-- The original forwarding body composes with the original captured-square
source wrapper; no callback-success or inverse-correctness premise remains. -/
theorem inverse_refines : PortableInverseChallenges.actualInverseReturnsFieldInverse := by
  intro input
  exact InverseUsing.inverse_refines input

end BulksketchBridge.PortableInverse
