-- Original checked singleton entry points, with scoped register and memory bindings.
import Arithmetic.AvxEncode18Runtime
import Arithmetic.AvxSliceKernelGenerated

open Aeneas Aeneas.Std Result Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

variable (baseModel : AvxEncode18Runtime.Bases) (loadModel : AvxSquareRuntime.Load)
variable (storeModel : AvxSquareRuntime.Store)

local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "core.num.U64.to_ne_bytes" => X86PclmulRuntime.unsignedBytes
local notation "core.num.I64.from_ne_bytes" => X86PclmulRuntime.signedFromBytes
local notation "core.core_arch.x86.avx512f._mm512_set1_epi64" => Avx512Register.broadcast
local notation "core.core_arch.x86.avx512f._mm512_set_epi64" => AvxEncode18Runtime.set8
local notation "core.core_arch.x86.avx512f._mm512_permutexvar_epi64" => AvxEncode18Runtime.permute
local notation "core.core_arch.x86.avx512f._mm512_permutex2var_epi64" => AvxEncode18Runtime.permuteTwo
local notation "core.core_arch.x86.avx512f._mm512_mask_mov_epi64" => AvxEncode18Runtime.maskMove
local notation "core.core_arch.x86.avx512f._mm512_unpacklo_epi64" => (Avx512Register.unpack false)
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "backend.x86_vpclmul512.single_bases" => baseModel
local notation "backend.x86_vpclmul512.load" => loadModel
local notation "backend.x86_vpclmul512.store" => storeModel
local notation "backend.x86_vpclmul512.update_single_block" =>
  (backend.x86_vpclmul512.update_single_block loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::broadcast]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 750:0-752:1 -/
def backend.x86_vpclmul512.broadcast
  (LANE : Std.I64) (value : core.core_arch.x86.__m512i) :
  Result core.core_arch.x86.__m512i
  := do
  let mi ← core.core_arch.x86.avx512f._mm512_set1_epi64 LANE
  core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi value

/-- [bulksketch::backend::x86_vpclmul512::insert_single]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 712:0-747:1 -/
def backend.x86_vpclmul512.insert_single
  (C : Std.Usize) (odd : Slice Std.U64) (id : Std.U64) :
  Result (Slice Std.U64)
  := do
  let (odd1, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) odd
      { «end» := C }
  let base ← backend.x86_vpclmul512.single_bases id
  let a ← core.num.U64.to_ne_bytes id
  let i ← core.num.I64.from_ne_bytes a
  let x ← core.core_arch.x86.avx512f._mm512_set1_epi64 i
  let mi ← backend.x86_vpclmul512.broadcast 0#i64 base
  let b ← backend.x86_vpclmul512.multiply true x mi
  let a1 ← core.core_arch.x86.avx512f._mm512_unpacklo_epi64 x b
  let mi1 ← backend.x86_vpclmul512.broadcast 1#i64 base
  let b1 ← backend.x86_vpclmul512.multiply true a1 mi1
  let mi2 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 9#i64 8#i64 1#i64 0#i64 9#i64
      8#i64 1#i64 0#i64
  let a2 ← core.core_arch.x86.avx512f._mm512_permutex2var_epi64 a1 mi2 b1
  let mi3 ← backend.x86_vpclmul512.broadcast 2#i64 base
  let b2 ← backend.x86_vpclmul512.multiply true a2 mi3
  let mi4 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 11#i64 10#i64 9#i64 8#i64 3#i64
      2#i64 1#i64 0#i64
  let v0 ← core.core_arch.x86.avx512f._mm512_permutex2var_epi64 a2 mi4 b2
  let odd2 ← backend.x86_vpclmul512.update_single_block odd1 0#usize v0
  let mi5 ← backend.x86_vpclmul512.broadcast 3#i64 base
  let v1 ← backend.x86_vpclmul512.multiply true v0 mi5
  let odd3 ← backend.x86_vpclmul512.update_single_block odd2 8#usize v1
  let mi6 ← backend.x86_vpclmul512.broadcast 4#i64 base
  let v2 ← backend.x86_vpclmul512.multiply true v0 mi6
  let odd4 ← backend.x86_vpclmul512.update_single_block odd3 16#usize v2
  let v3 ← backend.x86_vpclmul512.multiply true v1 mi6
  let odd5 ← backend.x86_vpclmul512.update_single_block odd4 24#usize v3
  if C > 32#usize
  then
    let step ← backend.x86_vpclmul512.broadcast 5#i64 base
    let v4 ← backend.x86_vpclmul512.multiply true v0 step
    let v5 ← backend.x86_vpclmul512.multiply true v1 step
    let v6 ← backend.x86_vpclmul512.multiply true v2 step
    let v7 ← backend.x86_vpclmul512.multiply true v3 step
    let odd6 ← backend.x86_vpclmul512.update_single_block odd5 32#usize v4
    let odd7 ← backend.x86_vpclmul512.update_single_block odd6 40#usize v5
    let odd8 ← backend.x86_vpclmul512.update_single_block odd7 48#usize v6
    let odd9 ← backend.x86_vpclmul512.update_single_block odd8 56#usize v7
    let step1 ← backend.x86_vpclmul512.broadcast 6#i64 base
    let mi7 ← backend.x86_vpclmul512.multiply true v0 step1
    let odd10 ← backend.x86_vpclmul512.update_single_block odd9 64#usize mi7
    if C > 72#usize
    then
      let mi8 ← backend.x86_vpclmul512.multiply true v1 step1
      let odd11 ←
        backend.x86_vpclmul512.update_single_block odd10 72#usize mi8
      let mi9 ← backend.x86_vpclmul512.multiply true v2 step1
      let odd12 ←
        backend.x86_vpclmul512.update_single_block odd11 80#usize mi9
      let mi10 ← backend.x86_vpclmul512.multiply true v3 step1
      let odd13 ←
        backend.x86_vpclmul512.update_single_block odd12 88#usize mi10
      ok (index_mut_back odd13)
    else ok (index_mut_back odd10)
  else ok (index_mut_back odd5)

/-- [bulksketch::backend::x86_vpclmul512::insert_32]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 616:0-705:1 -/
def backend.x86_vpclmul512.insert_32
  (odd : Slice Std.U64) (id : Std.U64) : Result (Slice Std.U64) := do
  let (odd1, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) odd
      { «end» := 32#usize }
  let base ← backend.x86_vpclmul512.single_bases id
  let a ← core.num.U64.to_ne_bytes id
  let i ← core.num.I64.from_ne_bytes a
  let x ← core.core_arch.x86.avx512f._mm512_set1_epi64 i
  let mi ←
    core.core_arch.x86.avx512f._mm512_set_epi64 11#i64 10#i64 9#i64 0#i64 0#i64
      0#i64 0#i64 0#i64
  let mi1 ← core.core_arch.x86.avx512f._mm512_permutex2var_epi64 x mi base
  let mi2 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 4#i64 3#i64 2#i64 4#i64 3#i64
      2#i64 1#i64 0#i64
  let mi3 ← core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi2 base
  let first ← backend.x86_vpclmul512.multiply true mi1 mi3
  let mi4 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 1#i64 0#i64 2#i64 1#i64 0#i64
      1#i64 0#i64 0#i64
  let mi5 ← core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi4 first
  let mi6 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 4#i64 4#i64 3#i64 3#i64 3#i64
      2#i64 2#i64 1#i64
  let mi7 ← core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi6 base
  let second_low ← backend.x86_vpclmul512.multiply true mi5 mi7
  let mi8 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 6#i64 10#i64 0#i64 1#i64 0#i64
      0#i64 3#i64 2#i64
  let mi9 ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 first mi8 base
  let mi10 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 4#i64 4#i64 15#i64 14#i64
      14#i64 13#i64 4#i64 4#i64
  let mi11 ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 base mi10 first
  let second_high ← backend.x86_vpclmul512.multiply true mi9 mi11
  let mi12 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 0#i64 9#i64 0#i64 9#i64 8#i64
      0#i64 0#i64 0#i64
  let mi13 ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 second_low mi12 first
  let mi14 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 15#i64 15#i64 0#i64 0#i64 0#i64
      4#i64 14#i64 3#i64
  let mi15 ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 base mi14 first
  let mi16 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 0#i64 0#i64 6#i64 6#i64 6#i64
      0#i64 0#i64 0#i64
  let mi17 ←
    core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi16 second_high
  let mi18 ← core.core_arch.x86.avx512f._mm512_mask_mov_epi64 mi15 56#u8 mi17
  let third_low ← backend.x86_vpclmul512.multiply true mi13 mi18
  let mi19 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 0#i64 0#i64 0#i64 0#i64 8#i64
      1#i64 0#i64 2#i64
  let mi20 ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 first mi19 second_low
  let mi21 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 0#i64 0#i64 0#i64 0#i64 15#i64
      15#i64 15#i64 7#i64
  let mi22 ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 first mi21 second_high
  let third_high ← backend.x86_vpclmul512.multiply true mi20 mi22
  let mi23 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 0#i64 0#i64 0#i64 10#i64 0#i64
      9#i64 8#i64 0#i64
  let mi24 ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 x mi23 first
  let mi25 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 0#i64 2#i64 1#i64 0#i64 0#i64
      0#i64 0#i64 0#i64
  let mi26 ←
    core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi25 second_low
  let mi27 ←
    core.core_arch.x86.avx512f._mm512_mask_mov_epi64 mi24 104#u8 mi26
  let mi28 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 2#i64 0#i64 0#i64 0#i64 0#i64
      0#i64 0#i64 0#i64
  let mi29 ←
    core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi28 second_high
  let value ←
    core.core_arch.x86.avx512f._mm512_mask_mov_epi64 mi27 128#u8 mi29
  let (dst, index_mut_back1) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) odd1
      { start := 0#usize, «end» := 8#usize }
  let mi30 ← backend.x86_vpclmul512.load dst
  let mi31 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi30 value
  let dst1 ← backend.x86_vpclmul512.store dst mi31
  let mi32 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 0#i64 0#i64 0#i64 13#i64 0#i64
      12#i64 11#i64 3#i64
  let mi33 ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 first mi32 second_low
  let mi34 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 1#i64 0#i64 0#i64 0#i64 0#i64
      0#i64 0#i64 0#i64
  let mi35 ←
    core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi34 third_low
  let mi36 ←
    core.core_arch.x86.avx512f._mm512_mask_mov_epi64 mi33 136#u8 mi35
  let mi37 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 0#i64 4#i64 3#i64 0#i64 0#i64
      0#i64 0#i64 0#i64
  let mi38 ←
    core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi37 second_high
  let value1 ←
    core.core_arch.x86.avx512f._mm512_mask_mov_epi64 mi36 96#u8 mi38
  let odd2 := index_mut_back1 dst1
  let (dst2, index_mut_back2) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) odd2
      { start := 8#usize, «end» := 16#usize }
  let mi39 ← backend.x86_vpclmul512.load dst2
  let mi40 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi39 value1
  let dst3 ← backend.x86_vpclmul512.store dst2 mi40
  let mi41 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 0#i64 0#i64 0#i64 0#i64 0#i64
      15#i64 14#i64 4#i64
  let mi42 ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 first mi41 second_low
  let mi43 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 5#i64 4#i64 3#i64 0#i64 2#i64
      0#i64 0#i64 0#i64
  let mi44 ←
    core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi43 third_low
  let mi45 ←
    core.core_arch.x86.avx512f._mm512_mask_mov_epi64 mi42 232#u8 mi44
  let mi46 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 0#i64 0#i64 0#i64 0#i64 0#i64
      0#i64 0#i64 0#i64
  let mi47 ←
    core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi46 second_high
  let value2 ←
    core.core_arch.x86.avx512f._mm512_mask_mov_epi64 mi45 16#u8 mi47
  let odd3 := index_mut_back2 dst3
  let (dst4, index_mut_back3) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) odd3
      { start := 16#usize, «end» := 24#usize }
  let mi48 ← backend.x86_vpclmul512.load dst4
  let mi49 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi48 value2
  let dst5 ← backend.x86_vpclmul512.store dst4 mi49
  let mi50 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 0#i64 0#i64 0#i64 0#i64 15#i64
      14#i64 5#i64 1#i64
  let mi51 ←
    core.core_arch.x86.avx512f._mm512_permutex2var_epi64 second_high mi50
      third_low
  let mi52 ←
    core.core_arch.x86.avx512f._mm512_set_epi64 3#i64 2#i64 1#i64 0#i64 0#i64
      0#i64 0#i64 0#i64
  let mi53 ←
    core.core_arch.x86.avx512f._mm512_permutexvar_epi64 mi52 third_high
  let value3 ←
    core.core_arch.x86.avx512f._mm512_mask_mov_epi64 mi51 240#u8 mi53
  let odd4 := index_mut_back3 dst5
  let (dst6, index_mut_back4) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) odd4
      { start := 24#usize, «end» := 32#usize }
  let mi54 ← backend.x86_vpclmul512.load dst6
  let mi55 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi54 value3
  let dst7 ← backend.x86_vpclmul512.store dst6 mi55
  let odd5 := index_mut_back4 dst7
  ok (index_mut_back odd5)

end bulksketch
