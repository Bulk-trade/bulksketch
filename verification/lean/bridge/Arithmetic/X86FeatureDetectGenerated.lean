-- Exact original feature-detection declarations with scoped register observations.
import Arithmetic.X86FeatureDetectRuntime
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

section
variable (snapshot : X86FeatureDetectRuntime.Snapshot)

local notation "core.core_arch.x86.cpuid.__cpuid" => X86FeatureDetectRuntime.cpuid snapshot
local notation "core.core_arch.x86.cpuid.__cpuid_count" => X86FeatureDetectRuntime.cpuidCount snapshot
local notation "core.core_arch.x86.xsave._xgetbv" => X86FeatureDetectRuntime.xgetbv snapshot

/-- [bulksketch::backend::detect::vpclmul512_supported]:
    Source: 'src/backend/detect.rs', lines 99:0-101:1 -/
def backend.detect.vpclmul512_supported
  (cpu : Bool) (os : Bool) : Result Bool := do
  if cpu
  then ok os
  else ok false

/-- [bulksketch::backend::x86_vpclmul512::detect]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 36:0-47:1 -/
def backend.x86_vpclmul512.detect : Result Bool := do
  let leaf1 ← core.core_arch.x86.cpuid.__cpuid 1#u32
  let leaf7 ← core.core_arch.x86.cpuid.__cpuid_count 7#u32 0#u32
  let i ← 1#u32 <<< 16#i32
  let i1 ← lift (leaf7.ebx &&& i)
  let cpu ←
    if i1 != 0#u32
    then
      do
      let i2 ← 1#u32 <<< 10#i32
      let i3 ← lift (leaf7.ecx &&& i2)
      ok (i3 != 0#u32)
    else ok false
  let i2 ← 3#u32 <<< 26#i32
  let i3 ← lift (leaf1.ecx &&& i2)
  let os ←
    if i3 = i2
    then
      do
      let i4 ← core.core_arch.x86.xsave._xgetbv 0#u32
      let i5 ← lift (i4 &&& 230#u64)
      ok (i5 = 230#u64)
    else ok false
  backend.detect.vpclmul512_supported cpu os

end

end bulksketch
