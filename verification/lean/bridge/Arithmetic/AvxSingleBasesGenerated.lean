-- Exact stock original insertion-table type and single_bases declaration.
import Arithmetic.AvxSquareRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

/-- [bulksketch::backend::x86_vpclmul512::InsertionBases]
    Source: 'src/backend/x86_vpclmul512.rs', lines 477:0-480:1 -/
structure backend.x86_vpclmul512.InsertionBases where
  six : Array (Array (Array Std.U64 8#usize) 64#usize) 9#usize
  five : Array (Array (Array Std.U64 8#usize) 32#usize) 2#usize

variable (tableModel : Result backend.x86_vpclmul512.InsertionBases)
variable (loadModel : AvxSquareRuntime.Load)

local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "backend.x86_vpclmul512.INSERT_BASES" => tableModel
local notation "backend.x86_vpclmul512.load" => loadModel

/-- [bulksketch::backend::x86_vpclmul512::single_bases]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 522:0-539:1 -/
def backend.x86_vpclmul512.single_bases
  (id : Std.U64) : Result core.core_arch.x86.__m512i := do
  let i ← lift (id &&& 63#u64)
  let i1 ← lift (UScalar.cast .Usize i)
  let ib ← backend.x86_vpclmul512.INSERT_BASES
  let a ← Array.index_usize ib.six 0#usize
  let a1 ← Array.index_usize a i1
  let s ← lift (Array.to_slice a1)
  let v0 ← backend.x86_vpclmul512.load s
  let i2 ← id >>> 6#i32
  let i3 ← lift (i2 &&& 63#u64)
  let i4 ← lift (UScalar.cast .Usize i3)
  let a2 ← Array.index_usize ib.six 1#usize
  let a3 ← Array.index_usize a2 i4
  let s1 ← lift (Array.to_slice a3)
  let v1 ← backend.x86_vpclmul512.load s1
  let i5 ← id >>> 12#i32
  let i6 ← lift (i5 &&& 63#u64)
  let i7 ← lift (UScalar.cast .Usize i6)
  let a4 ← Array.index_usize ib.six 2#usize
  let a5 ← Array.index_usize a4 i7
  let s2 ← lift (Array.to_slice a5)
  let v2 ← backend.x86_vpclmul512.load s2
  let i8 ← id >>> 18#i32
  let i9 ← lift (i8 &&& 63#u64)
  let i10 ← lift (UScalar.cast .Usize i9)
  let a6 ← Array.index_usize ib.six 3#usize
  let a7 ← Array.index_usize a6 i10
  let s3 ← lift (Array.to_slice a7)
  let v3 ← backend.x86_vpclmul512.load s3
  let i11 ← id >>> 24#i32
  let i12 ← lift (i11 &&& 63#u64)
  let i13 ← lift (UScalar.cast .Usize i12)
  let a8 ← Array.index_usize ib.six 4#usize
  let a9 ← Array.index_usize a8 i13
  let s4 ← lift (Array.to_slice a9)
  let v4 ← backend.x86_vpclmul512.load s4
  let i14 ← id >>> 30#i32
  let i15 ← lift (i14 &&& 63#u64)
  let i16 ← lift (UScalar.cast .Usize i15)
  let a10 ← Array.index_usize ib.six 5#usize
  let a11 ← Array.index_usize a10 i16
  let s5 ← lift (Array.to_slice a11)
  let v5 ← backend.x86_vpclmul512.load s5
  let i17 ← id >>> 36#i32
  let i18 ← lift (i17 &&& 63#u64)
  let i19 ← lift (UScalar.cast .Usize i18)
  let a12 ← Array.index_usize ib.six 6#usize
  let a13 ← Array.index_usize a12 i19
  let s6 ← lift (Array.to_slice a13)
  let v6 ← backend.x86_vpclmul512.load s6
  let i20 ← id >>> 42#i32
  let i21 ← lift (i20 &&& 63#u64)
  let i22 ← lift (UScalar.cast .Usize i21)
  let a14 ← Array.index_usize ib.six 7#usize
  let a15 ← Array.index_usize a14 i22
  let s7 ← lift (Array.to_slice a15)
  let v7 ← backend.x86_vpclmul512.load s7
  let i23 ← id >>> 48#i32
  let i24 ← lift (i23 &&& 63#u64)
  let i25 ← lift (UScalar.cast .Usize i24)
  let a16 ← Array.index_usize ib.six 8#usize
  let a17 ← Array.index_usize a16 i25
  let s8 ← lift (Array.to_slice a17)
  let v8 ← backend.x86_vpclmul512.load s8
  let i26 ← id >>> 54#i32
  let i27 ← lift (i26 &&& 31#u64)
  let i28 ← lift (UScalar.cast .Usize i27)
  let a18 ← Array.index_usize ib.five 0#usize
  let a19 ← Array.index_usize a18 i28
  let s9 ← lift (Array.to_slice a19)
  let v9 ← backend.x86_vpclmul512.load s9
  let i29 ← id >>> 59#i32
  let i30 ← lift (UScalar.cast .Usize i29)
  let a20 ← Array.index_usize ib.five 1#usize
  let a21 ← Array.index_usize a20 i30
  let s10 ← lift (Array.to_slice a21)
  let v10 ← backend.x86_vpclmul512.load s10
  let mi ← core.core_arch.x86.avx512f._mm512_xor_si512 v1 v2
  let a22 ← core.core_arch.x86.avx512f._mm512_xor_si512 v0 mi
  let mi1 ← core.core_arch.x86.avx512f._mm512_xor_si512 v4 v5
  let b ← core.core_arch.x86.avx512f._mm512_xor_si512 v3 mi1
  let mi2 ← core.core_arch.x86.avx512f._mm512_xor_si512 v7 v8
  let c ← core.core_arch.x86.avx512f._mm512_xor_si512 v6 mi2
  let d ← core.core_arch.x86.avx512f._mm512_xor_si512 v9 v10
  let mi3 ← core.core_arch.x86.avx512f._mm512_xor_si512 a22 b
  let mi4 ← core.core_arch.x86.avx512f._mm512_xor_si512 c d
  core.core_arch.x86.avx512f._mm512_xor_si512 mi3 mi4

end bulksketch
