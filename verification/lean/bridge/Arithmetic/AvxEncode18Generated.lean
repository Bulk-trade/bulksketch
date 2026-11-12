-- Exact declarations from checked stock captures.
import Arithmetic.AvxEncode18Runtime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

variable (baseModel : AvxEncode18Runtime.Bases)
variable (storeModel : AvxSquareRuntime.Store)

local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "core.core_arch.x86.avx512f._mm512_set1_epi64" => Avx512Register.broadcast
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "core.core_arch.x86.avx512f._mm512_set_epi64" => AvxEncode18Runtime.set8
local notation "core.core_arch.x86.avx512f._mm512_permutexvar_epi64" => AvxEncode18Runtime.permute
local notation "core.core_arch.x86.avx512f._mm512_permutex2var_epi64" => AvxEncode18Runtime.permuteTwo
local notation "core.core_arch.x86.avx512f._mm512_mask_mov_epi64" => AvxEncode18Runtime.maskMove
local notation "core.num.U64.to_ne_bytes" => X86PclmulRuntime.unsignedBytes
local notation "core.num.I64.from_ne_bytes" => X86PclmulRuntime.signedFromBytes
local notation "backend.x86_vpclmul512.single_bases" => baseModel
local notation "backend.x86_vpclmul512.store" => storeModel

/-- [bulksketch::backend::x86_vpclmul512::powers_18]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 569:0-610:1 -/
def backend.x86_vpclmul512.powers_18
  (id : Std.U64) :
  Result (core.core_arch.x86.__m512i × core.core_arch.x86.__m512i ×
    core.core_arch.x86.__m512i)
  := do
  let a ← core.num.U64.to_ne_bytes id
  let i ← core.num.I64.from_ne_bytes a
  let x ← core.core_arch.x86.avx512f._mm512_set1_epi64 i
  let base ← backend.x86_vpclmul512.single_bases id
  let mi ←
    core.core_arch.x86.avx512f._mm512_set_epi64 2#i64 2#i64 2#i64 2#i64 2#i64
      2#i64 2#i64 2#i64
  let mi1 ← core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi base
  let mi2 ← core.core_arch.x86.avx512f._mm512_mask_mov_epi64 x 32#u8 mi1
  let mi3 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 3#i64 3#i64 3#i64 3#i64 3#i64
      3#i64 3#i64 3#i64
  let mi4 ← core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi3 base
  let mi5 ← core.core_arch.x86.avx512f._mm512_mask_mov_epi64 base 32#u8 mi4
  let first ← backend.x86_vpclmul512.multiply true mi2 mi5
  let mi6 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 5#i64 0#i64 2#i64 1#i64 0#i64
      1#i64 0#i64 0#i64
  let mi7 ← core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi6 first
  let mi8 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 5#i64 4#i64 3#i64 3#i64 3#i64
      2#i64 2#i64 1#i64
  let mi9 ← core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi8 base
  let second ← backend.x86_vpclmul512.multiply true mi7 mi9
  let mi10 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 5#i64 5#i64 5#i64 0#i64 3#i64
      3#i64 3#i64 2#i64
  let right ← core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi10 base
  let mi11 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 5#i64 5#i64 5#i64 5#i64 5#i64
      5#i64 5#i64 5#i64
  let mi12 ← core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi11 first
  let right1 ←
    core.core_arch.x86.avx512f._mm512_mask_mov_epi64 right 16#u8 mi12
  let mi13 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 7#i64 7#i64 7#i64 0#i64 2#i64
      1#i64 0#i64 0#i64
  let mi14 ← core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi13 second
  let third ← backend.x86_vpclmul512.multiply true mi14 right1
  let mi15 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 0#i64 10#i64 9#i64 2#i64 8#i64
      1#i64 0#i64 0#i64
  let low ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 first mi15 second
  let mi16 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 8#i64 6#i64 5#i64 4#i64 3#i64
      2#i64 1#i64 0#i64
  let low1 ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 low mi16 third
  let low2 ← core.core_arch.x86.avx512f._mm512_mask_mov_epi64 low1 1#u8 x
  let mi17 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 0#i64 0#i64 0#i64 13#i64 0#i64
      12#i64 11#i64 3#i64
  let high ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 first mi17 second
  let mi18 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 12#i64 11#i64 10#i64 4#i64
      9#i64 2#i64 1#i64 0#i64
  let high1 ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 high mi18 third
  let mi19 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 0#i64 0#i64 0#i64 0#i64 0#i64
      0#i64 14#i64 4#i64
  let tail ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 first mi19 second
  ok (low2, high1, tail)

local notation "backend.x86_vpclmul512.powers_18" => (backend.x86_vpclmul512.powers_18 baseModel)

/-- [bulksketch::backend::x86_vpclmul512::encode_18]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 552:0-565:1 -/
def backend.x86_vpclmul512.encode_18
  (odd : Slice Std.U64) (ids : Slice Std.U64) : Result (Slice Std.U64) := do
  let i ← Slice.index_usize ids 0#usize
  let (low, high, tail) ← backend.x86_vpclmul512.powers_18 i
  let i1 := Slice.len ids
  let (low1, high1, tail1) ←
    if i1 = 2#usize
    then
      do
      let i2 ← Slice.index_usize ids 1#usize
      let (other_low, other_high, other_tail) ←
        backend.x86_vpclmul512.powers_18 i2
      let low2 ← core.core_arch.x86.avx512f._mm512_xor_si512 low other_low
      let high2 ← core.core_arch.x86.avx512f._mm512_xor_si512 high other_high
      let tail2 ← core.core_arch.x86.avx512f._mm512_xor_si512 tail other_tail
      ok (low2, high2, tail2)
    else ok (low, high, tail)
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) odd
      { «end» := 18#usize }
  let ((low_words, rest), split_at_mut_back) ←
    core.slice.Slice.split_at_mut s 8#usize
  let ((high_words, tail_words), split_at_mut_back1) ←
    core.slice.Slice.split_at_mut rest 8#usize
  let low_words1 ← backend.x86_vpclmul512.store low_words low1
  let high_words1 ← backend.x86_vpclmul512.store high_words high1
  let tail_words1 ← backend.x86_vpclmul512.store tail_words tail1
  let rest1 := split_at_mut_back1 (high_words1, tail_words1)
  let s1 := split_at_mut_back (low_words1, rest1)
  ok (index_mut_back s1)

end bulksketch
