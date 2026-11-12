-- Exact original horizontal reduction from checked stock extraction.
import Arithmetic.AvxSquareRuntime

open Aeneas Aeneas.Std Result ControlFlow Error

namespace Aeneas.Std.AvxHorizontalRuntime

open Avx512Register

abbrev Pair128 := BitVec 64 × BitVec 64

def selectPair (mask : I32) (index : Fin 4) : Fin 4 :=
  ⟨(mask.bv.toNat >>> (2 * index.val)) % 4, Nat.mod_lt _ (by decide)⟩

def shufflePairs (mask : I32) (left right : Word512) : Result Word512 :=
  .ok (fun pair high => if pair.val < 2 then left (selectPair mask pair) high else right (selectPair mask pair) high)

/-- The original body uses only 0x4e, swapping the 64-bit halves of each
128-bit pair. The scope here is that immediate. -/
def shuffleDwords (mask : I32) (value : Word512) : Result Word512 :=
  if mask = 78#i32 then .ok (fun pair high => value pair (!high)) else .fail .panic

def lowPair (value : Word512) : Result Pair128 := .ok (value 0 false, value 0 true)

def lowWord (value : Pair128) : Result I64 := .ok ⟨value.1⟩

end Aeneas.Std.AvxHorizontalRuntime

namespace bulksketch

local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "core.core_arch.x86.avx512f._mm512_shuffle_i64x2" => AvxHorizontalRuntime.shufflePairs
local notation "core.core_arch.x86.avx512f._mm512_shuffle_epi32" => AvxHorizontalRuntime.shuffleDwords
local notation "core.core_arch.x86.avx512f._mm512_castsi512_si128" => AvxHorizontalRuntime.lowPair
local notation "core.core_arch.x86_64.sse2._mm_cvtsi128_si64" => AvxHorizontalRuntime.lowWord
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "core.num.I64.to_ne_bytes" => X86PclmulRuntime.signedBytes
local notation "core.num.U64.from_ne_bytes" => X86PclmulRuntime.unsignedFromBytes

/-- [bulksketch::backend::x86_vpclmul512::horizontal_xor]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 253:0-258:1 -/
def backend.x86_vpclmul512.horizontal_xor
  (value : core.core_arch.x86.__m512i) : Result Std.U64 := do
  let mi ← core.core_arch.x86.avx512f._mm512_shuffle_i64x2 78#i32 value value
  let value1 ← core.core_arch.x86.avx512f._mm512_xor_si512 value mi
  let mi1 ←
    core.core_arch.x86.avx512f._mm512_shuffle_i64x2 177#i32 value1 value1
  let value2 ← core.core_arch.x86.avx512f._mm512_xor_si512 value1 mi1
  let mi2 ← core.core_arch.x86.avx512f._mm512_shuffle_epi32 78#i32 value2
  let value3 ← core.core_arch.x86.avx512f._mm512_xor_si512 value2 mi2
  let mi3 ← core.core_arch.x86.avx512f._mm512_castsi512_si128 value3
  let i ← core.core_arch.x86_64.sse2._mm_cvtsi128_si64 mi3
  let a ← core.num.I64.to_ne_bytes i
  core.num.U64.from_ne_bytes a

end bulksketch
