import Arithmetic.X86PclmulSliceGenerated
import BulksketchBridge.MutableZipPrefix
import BulksketchBridge.PortableSliceChallenges

namespace BulksketchBridge.X86PclmulSliceChallenges

open Aeneas.Std BulksketchBridge.MutableZip

abbrev dictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
abbrev scaledWord := PortableSliceChallenges.scaleValue

/-- The private helpers accept both reduction selectors and preserve unmatched
destination words when either slice is shorter. -/
def ScaleRefines : Prop :=
  ∀ (cl : Bool) (dst src : Slice U64) (scale : U64),
    bulksketch.backend.x86_pclmul.scale_xor cl dictionary dst src scale =
      Result.ok (mapPrefixFrom dst src (scaledWord scale) 0)

def SquareRefines : Prop :=
  ∀ (cl : Bool) (dst src : Slice U64),
    bulksketch.backend.x86_pclmul.square_slice cl dictionary dst src =
      Result.ok (mapPrefixFrom dst src (fun _ source => Square.expectedWord source) 0)

def ScaleEntryRefines : Prop :=
  ∀ (dst src : Slice U64) (scale : U64),
    bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.scale_xor
      dictionary dst src scale =
        if dst.length = src.length then Result.ok (mapPrefixFrom dst src (scaledWord scale) 0)
        else Result.fail Error.panic

def SquareEntryRefines : Prop :=
  ∀ dst src : Slice U64,
    bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.square_slice
      dictionary dst src =
        if dst.length = src.length then
          Result.ok (mapPrefixFrom dst src (fun _ source => Square.expectedWord source) 0)
        else Result.fail Error.panic

def XorEntryRefines : Prop :=
  ∀ dst src : Slice U64,
    bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.xor_assign
      dictionary dst src =
        if dst.length = src.length then Result.ok (mapPrefixFrom dst src (· ^^^ ·) 0)
        else Result.fail Error.panic

end BulksketchBridge.X86PclmulSliceChallenges
