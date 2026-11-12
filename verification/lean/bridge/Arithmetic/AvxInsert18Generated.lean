-- Exact original AVX insert_18 declaration from checked stock extraction.
import Arithmetic.AvxEncode18Generated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

variable (baseModel : AvxEncode18Runtime.Bases)
variable (loadModel : AvxSquareRuntime.Load)
variable (storeModel : AvxSquareRuntime.Store)

local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "backend.x86_vpclmul512.powers_18" => (backend.x86_vpclmul512.powers_18 baseModel)
local notation "backend.x86_vpclmul512.load" => loadModel
local notation "backend.x86_vpclmul512.store" => storeModel

/-- [bulksketch::backend::x86_vpclmul512::insert_18]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 542:0-549:1 -/
def backend.x86_vpclmul512.insert_18
  (odd : Slice Std.U64) (id : Std.U64) : Result (Slice Std.U64) := do
  let (low, high, tail) ← backend.x86_vpclmul512.powers_18 id
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) odd
      { «end» := 18#usize }
  let ((low_words, rest), split_at_mut_back) ←
    core.slice.Slice.split_at_mut s 8#usize
  let ((high_words, tail_words), split_at_mut_back1) ←
    core.slice.Slice.split_at_mut rest 8#usize
  let mi ← backend.x86_vpclmul512.load low_words
  let mi1 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi low
  let low_words1 ← backend.x86_vpclmul512.store low_words mi1
  let mi2 ← backend.x86_vpclmul512.load high_words
  let mi3 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi2 high
  let high_words1 ← backend.x86_vpclmul512.store high_words mi3
  let mi4 ← backend.x86_vpclmul512.load tail_words
  let mi5 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi4 tail
  let tail_words1 ← backend.x86_vpclmul512.store tail_words mi5
  let rest1 := split_at_mut_back1 (high_words1, tail_words1)
  let s1 := split_at_mut_back (low_words1, rest1)
  ok (index_mut_back s1)

end bulksketch
