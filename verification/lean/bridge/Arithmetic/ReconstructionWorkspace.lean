import Arithmetic.ReconstructionTypes
import BulksketchBridge.WorkspaceAdmission

namespace BulksketchBridge.Reconstruction

open Aeneas.Std

def workspaceLengths (workspace : bulksketch.decode.scratch.RowWorkspace) : WorkspaceAdmission.Lengths :=
  { syndromes := workspace.syndromes.length
    bm := workspace.bm.length
    polynomials := workspace.polynomials.length
    factors := workspace.factors.length
    squareTable := workspace.square_table.length
    verification := workspace.verification.length
    roots := workspace.roots.length
    raw := workspace.raw.length
    stack := workspace.stack.length }

def checkWorkspace (workspace : bulksketch.decode.scratch.RowWorkspace) (capacity budget : Usize) :
    Result (core.result.Result Unit bulksketch.types.DecodeError) :=
  .ok (WorkspaceAdmission.runOriginal workspaceLengths workspace capacity budget).1

end BulksketchBridge.Reconstruction
