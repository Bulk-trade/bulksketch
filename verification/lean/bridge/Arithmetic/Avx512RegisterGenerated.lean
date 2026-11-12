-- Exact original source declarations. Local notation binds the AVX-512 register model.
import Arithmetic.Avx512RegisterRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

local notation "core.core_arch.x86.__m512i" => Aeneas.Std.Avx512Register.Word512
local notation "core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128" => Aeneas.Std.Avx512Register.clmul
local notation "core.core_arch.x86.avx512f._mm512_slli_epi64" => Aeneas.Std.Avx512Register.shiftLeft
local notation "core.core_arch.x86.avx512f._mm512_srli_epi64" => Aeneas.Std.Avx512Register.shiftRight
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Aeneas.Std.Avx512Register.xorWords
local notation "core.core_arch.x86.avx512f._mm512_set1_epi64" => Aeneas.Std.Avx512Register.broadcast
local notation "core.core_arch.x86.avx512f._mm512_unpacklo_epi64" => Aeneas.Std.Avx512Register.unpack false
local notation "core.core_arch.x86.avx512f._mm512_unpackhi_epi64" => Aeneas.Std.Avx512Register.unpack true

/-- [bulksketch::backend::x86_vpclmul512::reduce_shift::{closure}]
    Source: 'src/backend/x86_vpclmul512.rs', lines 266:15-274:5 -/
@[reducible]
def backend.x86_vpclmul512.reduce_shift.closure := Unit

/-- [bulksketch::backend::x86_vpclmul512::raw]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 209:0-214:1 -/
def backend.x86_vpclmul512.raw
  (a : core.core_arch.x86.__m512i) (b : core.core_arch.x86.__m512i) :
  Result (core.core_arch.x86.__m512i × core.core_arch.x86.__m512i)
  := do
  let mi ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 0#i32 a b
  let mi1 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 17#i32 a b
  ok (mi, mi1)

/-- [bulksketch::backend::x86_vpclmul512::reduce_shift::{impl core::ops::function::Fn<(core::core_arch::x86::__m512i,), core::core_arch::x86::__m512i> for bulksketch::backend::x86_vpclmul512::reduce_shift::{closure}}::call]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 266:15-274:5 -/
def
  backend.x86_vpclmul512.reduce_shift.closure.Insts.CoreOpsFunctionFnTuple__m512i__m512i.call
  (c : backend.x86_vpclmul512.reduce_shift.closure)
  (tupled_args : core.core_arch.x86.__m512i) :
  Result core.core_arch.x86.__m512i
  := do
  let mi ← core.core_arch.x86.avx512f._mm512_slli_epi64 1#u32 tupled_args
  let mi1 ← core.core_arch.x86.avx512f._mm512_slli_epi64 3#u32 tupled_args
  let mi2 ← core.core_arch.x86.avx512f._mm512_slli_epi64 4#u32 tupled_args
  let mi3 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi1 mi2
  let mi4 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi mi3
  core.core_arch.x86.avx512f._mm512_xor_si512 tupled_args mi4

/-- [bulksketch::backend::x86_vpclmul512::reduce_shift]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 261:0-276:1 -/
def backend.x86_vpclmul512.reduce_shift
  (lo : core.core_arch.x86.__m512i) (hi : core.core_arch.x86.__m512i) :
  Result core.core_arch.x86.__m512i
  := do
  let mi ← core.core_arch.x86.avx512f._mm512_srli_epi64 63#u32 hi
  let mi1 ← core.core_arch.x86.avx512f._mm512_srli_epi64 61#u32 hi
  let mi2 ← core.core_arch.x86.avx512f._mm512_srli_epi64 60#u32 hi
  let mi3 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi1 mi2
  let overflow ← core.core_arch.x86.avx512f._mm512_xor_si512 mi mi3
  let mi4 ←
    backend.x86_vpclmul512.reduce_shift.closure.Insts.CoreOpsFunctionFnTuple__m512i__m512i.call
      () hi
  let mi5 ←
    backend.x86_vpclmul512.reduce_shift.closure.Insts.CoreOpsFunctionFnTuple__m512i__m512i.call
      () overflow
  let mi6 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi4 mi5
  core.core_arch.x86.avx512f._mm512_xor_si512 lo mi6

/-- [bulksketch::backend::x86_vpclmul512::reduce_cl]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 279:0-284:1 -/
def backend.x86_vpclmul512.reduce_cl
  (product : core.core_arch.x86.__m512i) :
  Result core.core_arch.x86.__m512i
  := do
  let polynomial ← core.core_arch.x86.avx512f._mm512_set1_epi64 27#i64
  let fold ←
    core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 1#i32 product
      polynomial
  let overflow ←
    core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 1#i32 fold
      polynomial
  let mi ← core.core_arch.x86.avx512f._mm512_xor_si512 fold overflow
  core.core_arch.x86.avx512f._mm512_xor_si512 product mi

/-- [bulksketch::backend::x86_vpclmul512::multiply]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 287:0-297:1 -/
def backend.x86_vpclmul512.multiply
  (CL : Bool) (a : core.core_arch.x86.__m512i) (b : core.core_arch.x86.__m512i)
  :
  Result core.core_arch.x86.__m512i
  := do
  let (even, odd) ← backend.x86_vpclmul512.raw a b
  if CL
  then
    let mi ← backend.x86_vpclmul512.reduce_cl even
    let mi1 ← backend.x86_vpclmul512.reduce_cl odd
    core.core_arch.x86.avx512f._mm512_unpacklo_epi64 mi mi1
  else
    let mi ← core.core_arch.x86.avx512f._mm512_unpacklo_epi64 even odd
    let mi1 ← core.core_arch.x86.avx512f._mm512_unpackhi_epi64 even odd
    backend.x86_vpclmul512.reduce_shift mi mi1

end bulksketch
