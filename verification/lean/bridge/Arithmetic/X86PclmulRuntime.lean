import Aeneas
import BulksketchProofs.Field.CLMulSpec

namespace Aeneas.Std.X86PclmulRuntime

open BulksketchProofs.Field

abbrev Xmm := BitVec 128

def low64 (register : Xmm) : BitVec 64 := register.setWidth 64

def high64 (register : Xmm) : BitVec 64 := (register >>> 64).setWidth 64

/-- The imm8 selects one word from each operand. Bits zero and four select
the upper word of the first and second operand, respectively. -/
def clmul (immediate : I32) (left right : Xmm) : Result Xmm :=
  .ok (clmul128 (if immediate.bv.getLsbD 0 then high64 left else low64 left)
    (if immediate.bv.getLsbD 4 then high64 right else low64 right))

/-- Shift the complete register right by the encoded byte count. -/
def shiftBytes (immediate : I32) (register : Xmm) : Result Xmm :=
  .ok (register >>> (8 * (immediate.bv.setWidth 8).toNat))

def xor (left right : Xmm) : Result Xmm := .ok (left ^^^ right)

def moveIn (word : I64) : Result Xmm := .ok (word.bv.setWidth 128)

def moveOut (register : Xmm) : Result I64 := .ok ⟨low64 register⟩

/-- Native byte order for the x86 extraction target. -/
def unsignedBytes (word : U64) : Result (Array U8 8#usize) :=
  .ok (core.num.U64.to_le_bytes word)

def signedBytes (word : I64) : Result (Array U8 8#usize) :=
  .ok (core.num.I64.to_le_bytes word)

def unsignedFromBytes (bytes : Array U8 8#usize) : Result U64 :=
  .ok (core.num.U64.from_le_bytes bytes)

def signedFromBytes (bytes : Array U8 8#usize) : Result I64 :=
  .ok (core.num.I64.from_le_bytes bytes)

end Aeneas.Std.X86PclmulRuntime
