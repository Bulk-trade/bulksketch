-- Generated from the frozen AVX xor_assign LLBC by project.py.
import BulksketchBridge.AvxXorLlbcRuntime

namespace BulksketchBridge.AvxXorLlbc

def program : Program :=
  ⟨8, 8, [.loadLeft, .loadRight, .xor, .store]⟩

end BulksketchBridge.AvxXorLlbc
