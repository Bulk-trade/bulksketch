import Arithmetic.X86LaneMaskGenerated

namespace BulksketchBridge.X86LaneMask

open Aeneas.Std

/-- Exact low-lane mask on the admitted lengths of the x86 source helper. -/
def ActualMaskReturnsLowLanes : Prop :=
  ∀ len : Usize, len.val ≤ 8 → ∃ output : U8,
    bulksketch.backend.x86_vpclmul512.mask len = Result.ok output ∧
    output.val = 2 ^ len.val - 1 ∧
    ∀ lane : Nat, lane < 8 → output.bv.getLsbD lane = decide (lane < len.val)

end BulksketchBridge.X86LaneMask
