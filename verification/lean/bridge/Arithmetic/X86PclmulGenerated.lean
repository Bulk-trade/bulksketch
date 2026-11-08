-- Exact original scalar x86 declarations with scoped x86 value bindings.
import Arithmetic.Funs
import Arithmetic.X86PclmulRuntime
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

local notation "core.core_arch.x86.__m128i" => X86PclmulRuntime.Xmm
local notation "core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128" => X86PclmulRuntime.clmul
local notation "core.core_arch.x86.sse2._mm_srli_si128" => X86PclmulRuntime.shiftBytes
local notation "core.core_arch.x86.sse2._mm_xor_si128" => X86PclmulRuntime.xor
local notation "core.core_arch.x86_64.sse2._mm_cvtsi64_si128" => X86PclmulRuntime.moveIn
local notation "core.core_arch.x86_64.sse2._mm_cvtsi128_si64" => X86PclmulRuntime.moveOut
local notation "core.num.U64.to_ne_bytes" => X86PclmulRuntime.unsignedBytes
local notation "core.num.I64.to_ne_bytes" => X86PclmulRuntime.signedBytes
local notation "core.num.U64.from_ne_bytes" => X86PclmulRuntime.unsignedFromBytes
local notation "core.num.I64.from_ne_bytes" => X86PclmulRuntime.signedFromBytes

/-- [bulksketch::backend::x86_pclmul::low]:
    Source: 'src/backend/x86_pclmul.rs', lines 124:0-127:1 -/
def backend.x86_pclmul.low
  (product : core.core_arch.x86.__m128i) : Result Std.U64 := do
  let i ← core.core_arch.x86_64.sse2._mm_cvtsi128_si64 product
  let a ← core.num.I64.to_ne_bytes i
  core.num.U64.from_ne_bytes a

/-- [bulksketch::backend::x86_pclmul::words]:
    Source: 'src/backend/x86_pclmul.rs', lines 130:0-137:1 -/
def backend.x86_pclmul.words
  (product : core.core_arch.x86.__m128i) : Result types.RawProduct := do
  let high ← core.core_arch.x86.sse2._mm_srli_si128 8#i32 product
  let i ← backend.x86_pclmul.low product
  let i1 ← backend.x86_pclmul.low high
  ok { lo := i, hi := i1 }

/-- [bulksketch::backend::x86_pclmul::word]:
    Source: 'src/backend/x86_pclmul.rs', lines 118:0-121:1 -/
def backend.x86_pclmul.word
  (a : Std.U64) : Result core.core_arch.x86.__m128i := do
  let a1 ← core.num.U64.to_ne_bytes a
  let i ← core.num.I64.from_ne_bytes a1
  core.core_arch.x86_64.sse2._mm_cvtsi64_si128 i

/-- [bulksketch::backend::x86_pclmul::reduced]:
    Source: 'src/backend/x86_pclmul.rs', lines 147:0-156:1 -/
def backend.x86_pclmul.reduced
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (product : core.core_arch.x86.__m128i) :
  Result core.core_arch.x86.__m128i
  := do
  if CL
  then
    let i ← fieldBinaryFieldInst.BITS
    if i = 64#u32
    then
      let i1 ← fieldBinaryFieldInst.MODULUS_LOW
      let modulus ← backend.x86_pclmul.word i1
      let first ←
        core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 1#i32 product modulus
      let second ←
        core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 1#i32 first modulus
      let mi ← core.core_arch.x86.sse2._mm_xor_si128 product first
      core.core_arch.x86.sse2._mm_xor_si128 mi second
    else
      let rp ← backend.x86_pclmul.words product
      let i1 ← field.gf64.reduce fieldBinaryFieldInst rp
      backend.x86_pclmul.word i1
  else
    let rp ← backend.x86_pclmul.words product
    let i ← field.gf64.reduce fieldBinaryFieldInst rp
    backend.x86_pclmul.word i

/-- [bulksketch::backend::x86_pclmul::multiply]:
    Source: 'src/backend/x86_pclmul.rs', lines 160:0-164:1 -/
def backend.x86_pclmul.multiply
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (a : Std.U64) (b : Std.U64) :
  Result Std.U64
  := do
  let mi ← backend.x86_pclmul.word a
  let mi1 ← backend.x86_pclmul.word b
  let product ←
    core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 0#i32 mi mi1
  let mi2 ← backend.x86_pclmul.reduced CL fieldBinaryFieldInst product
  backend.x86_pclmul.low mi2

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_pclmul::Pclmul}::mul]:
    Source: 'src/backend/x86_pclmul.rs', lines 35:4-38:5 -/
def backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.mul
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64)
  (b : Std.U64) :
  Result Std.U64
  := do
  backend.x86_pclmul.multiply true fieldBinaryFieldInst a b

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_pclmul::Pclmul}::square]:
    Source: 'src/backend/x86_pclmul.rs', lines 40:4-43:5 -/
def backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.square
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64) :
  Result Std.U64
  := do
  backend.x86_pclmul.multiply true fieldBinaryFieldInst a a

/-- [bulksketch::backend::x86_pclmul::raw_product]:
    Source: 'src/backend/x86_pclmul.rs', lines 141:0-143:1 -/
def backend.x86_pclmul.raw_product
  (a : Std.U64) (b : Std.U64) : Result types.RawProduct := do
  let mi ← backend.x86_pclmul.word a
  let mi1 ← backend.x86_pclmul.word b
  let mi2 ← core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 0#i32 mi mi1
  backend.x86_pclmul.words mi2

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_pclmul::Pclmul}::raw_mul]:
    Source: 'src/backend/x86_pclmul.rs', lines 68:4-71:5 -/
def backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.raw_mul
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (a : Std.U64)
  (b : Std.U64) :
  Result types.RawProduct
  := do
  backend.x86_pclmul.raw_product a b

end bulksketch
