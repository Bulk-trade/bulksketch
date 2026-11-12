-- The three exact original declarations from the checked stock extraction.
import Arithmetic.AvxSquareRuntime

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

set_option linter.dupNamespace false
set_option linter.unusedVariables false

variable (loadModel : Aeneas.Std.AvxSquareRuntime.Load)
variable (storeModel : Aeneas.Std.AvxSquareRuntime.Store)

local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "core.core_arch.x86.avx512f._mm512_set1_epi64" => Avx512Register.broadcast
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "core.num.U64.to_ne_bytes" => X86PclmulRuntime.unsignedBytes
local notation "core.num.I64.from_ne_bytes" => X86PclmulRuntime.signedFromBytes
local notation "backend.x86_vpclmul512.load" => loadModel
local notation "backend.x86_vpclmul512.store" => storeModel

/-- [bulksketch::backend::x86_vpclmul512::multiply_linear]: loop body 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 823:4-832:5 -/
@[rust_loop_body]
def backend.x86_vpclmul512.multiply_linear_loop.body
  (root : core.core_arch.x86.__m512i) (coefficients : Slice Std.U64)
  («end» : Std.Usize) :
  Result (ControlFlow ((Slice Std.U64) × Std.Usize) (Slice Std.U64))
  := do
  if «end» > 1#usize
  then
    let i ← lift (core.num.Usize.saturating_sub «end» 8#usize)
    let start ← lift (core.cmp.impls.OrdUsize.max i 1#usize)
    let s ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U64) coefficients { start, «end» }
    let mi ← backend.x86_vpclmul512.load s
    let i1 ← start - 1#usize
    let i2 ← «end» - 1#usize
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U64) coefficients { start := i1, «end» := i2 }
    let mi1 ← backend.x86_vpclmul512.load s1
    let mi2 ← backend.x86_vpclmul512.multiply true mi1 root
    let value ← core.core_arch.x86.avx512f._mm512_xor_si512 mi mi2
    let (s2, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) coefficients
        { start, «end» }
    let s3 ← backend.x86_vpclmul512.store s2 value
    let coefficients1 := index_mut_back s3
    ok (cont (coefficients1, start))
  else ok (done coefficients)

local notation "backend.x86_vpclmul512.multiply_linear_loop.body" => (backend.x86_vpclmul512.multiply_linear_loop.body loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::multiply_linear]: loop 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 823:4-832:5 -/
@[rust_loop]
def backend.x86_vpclmul512.multiply_linear_loop
  (coefficients : Slice Std.U64) (root : core.core_arch.x86.__m512i)
  («end» : Std.Usize) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (coefficients1, end1) =>
      backend.x86_vpclmul512.multiply_linear_loop.body root coefficients1 end1)
    (coefficients, «end»)

local notation "backend.x86_vpclmul512.multiply_linear_loop" => (backend.x86_vpclmul512.multiply_linear_loop loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::multiply_linear]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 820:0-833:1 -/
def backend.x86_vpclmul512.multiply_linear
  (coefficients : Slice Std.U64) (root : Std.U64) :
  Result (Slice Std.U64)
  := do
  let a ← core.num.U64.to_ne_bytes root
  let i ← core.num.I64.from_ne_bytes a
  let root1 ← core.core_arch.x86.avx512f._mm512_set1_epi64 i
  let «end» := Slice.len coefficients
  backend.x86_vpclmul512.multiply_linear_loop coefficients root1 «end»

end bulksketch
