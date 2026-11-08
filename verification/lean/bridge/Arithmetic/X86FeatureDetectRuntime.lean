module
public import Arithmetic.X86FeatureDetectTypes
@[expose] public section

namespace Aeneas.Std.X86FeatureDetectRuntime

abbrev CpuidResult := bulksketch.core.core_arch.x86.cpuid.CpuidResult

/-- Immutable register observations at the two source CPUID queries and XCR0.
The model faults an XGETBV call without the required XSAVE flags. -/
structure Snapshot where
  leaf1 : CpuidResult
  leaf7 : CpuidResult
  xcr0 : U64

def cpuid (snapshot : Snapshot) (leaf : U32) : Result CpuidResult :=
  if leaf = 1#u32 then .ok snapshot.leaf1 else .fail .undef

def cpuidCount (snapshot : Snapshot) (leaf subleaf : U32) : Result CpuidResult :=
  if leaf = 7#u32 ∧ subleaf = 0#u32 then .ok snapshot.leaf7 else .fail .undef

def xgetbv (snapshot : Snapshot) (index : U32) : Result U64 :=
  if index = 0#u32 ∧ snapshot.leaf1.ecx &&& 201326592#u32 = 201326592#u32 then
    .ok snapshot.xcr0
  else .fail .undef

end Aeneas.Std.X86FeatureDetectRuntime
