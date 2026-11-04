-- Native source pin: 0a5bda53f6b07fcae8acd870e2d0c4a246d207e6
-- Full reduce body normalized-token SHA256: a58b006da292ffefd3e6807af4ab39c80236c01926163cf56e278088525d86b4
-- Source gf64.rs SHA256: c5320b7121c3de4d3e7e04ecdc88a6ddf100901a534912b8811c6ff5add9aa27
import Init

/-! GENERATED from the pinned native Rust reduce::<Gf64> branch.
The AST translator and the Rust-to-BitVec semantic link are UNPROVED.
This definition is a model artifact, not a verified Rust implementation. -/

namespace BulksketchProofs.Generated

def reduceGf64 (lo hi : BitVec 64) : BitVec 64 :=
  let high := hi
  let overflow := (((high >>> 63) ^^^ (high >>> 61)) ^^^ (high >>> 60))
  ((((((((lo ^^^ high) ^^^ (high <<< 1)) ^^^ (high <<< 3)) ^^^ (high <<< 4)) ^^^ overflow) ^^^ (overflow <<< 1)) ^^^ (overflow <<< 3)) ^^^ (overflow <<< 4))

end BulksketchProofs.Generated
