import Aeneas
import BulksketchProofs.Field.CLMulSpec

namespace Aeneas.Std.Avx512Register

/-- Four 128-bit pairs, each indexed low (`false`) then high (`true`).
Pair indices increase with register bit positions. -/
abbrev Word512 := Fin 4 → Bool → BitVec 64

def low64 (word : BitVec 128) : BitVec 64 := word.setWidth 64

def high64 (word : BitVec 128) : BitVec 64 := (word >>> 64).setWidth 64

/-- VPCLMULQDQ selects one word in each input pair with immediate bits
zero and four, and writes the complete 128-bit polynomial product. -/
def clmul (immediate : I32) (left right : Word512) : Result Word512 :=
  .ok fun pair high =>
    let product := BulksketchProofs.Field.clmul128
      (left pair (immediate.bv.getLsbD 0)) (right pair (immediate.bv.getLsbD 4))
    if high then high64 product else low64 product

def shiftLeft (immediate : U32) (input : Word512) : Result Word512 :=
  .ok fun pair high => input pair high <<< immediate.val

def shiftRight (immediate : U32) (input : Word512) : Result Word512 :=
  .ok fun pair high => input pair high >>> immediate.val

def xorWords (left right : Word512) : Result Word512 :=
  .ok fun pair high => left pair high ^^^ right pair high

def broadcast (word : I64) : Result Word512 :=
  .ok fun _ _ => word.bv

/-- Interleave the selected half of each 128-bit pair. The low output
word comes from the left register and the high word from the right. -/
def unpack (highInput : Bool) (left right : Word512) : Result Word512 :=
  .ok fun pair high => if high then right pair highInput else left pair highInput

end Aeneas.Std.Avx512Register
