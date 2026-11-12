-- Exact original immutable static initializer declaration from stock checked extraction.
import Arithmetic.AvxInsertionBasesGenerated

open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

namespace bulksketch

/-- [bulksketch::backend::x86_vpclmul512::INSERT_BASES]
    Source: 'src/backend/x86_vpclmul512.rs', lines 519:0-519:56 -/
@[global_simps, irreducible]
def backend.x86_vpclmul512.INSERT_BASES
  : Result backend.x86_vpclmul512.InsertionBases :=
  backend.x86_vpclmul512.insertion_bases

end bulksketch
