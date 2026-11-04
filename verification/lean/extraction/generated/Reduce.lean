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
