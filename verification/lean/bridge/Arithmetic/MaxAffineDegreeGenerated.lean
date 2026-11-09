-- Exact original generated maximum preferred degree and loop.
import BulksketchBridge.AffinePredictor

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

/-- [bulksketch::decode::affine::MAX_PREFERRED_DEGREE]: loop body 0:
    Source: 'src/decode/affine.rs', lines 73:4-78:5 -/
@[rust_loop_body]
def decode.affine.MAX_PREFERRED_DEGREE_loop.body
  (degree : Std.Usize) (maximum : Std.Usize) :
  Result (ControlFlow (Std.Usize × Std.Usize) Std.Usize)
  := do
  if degree < 64#usize
  then
    let b ←
      decode.affine.preferred field.Gf64.Insts.BulksketchFieldBinaryField
        degree
    let maximum1 ← if b
                     then ok degree
                     else ok maximum
    let degree1 ← degree + 1#usize
    ok (cont (degree1, maximum1))
  else ok (done maximum)

/-- [bulksketch::decode::affine::MAX_PREFERRED_DEGREE]: loop 0:
    Source: 'src/decode/affine.rs', lines 73:4-78:5 -/
@[rust_loop]
def decode.affine.MAX_PREFERRED_DEGREE_loop
  (degree : Std.Usize) (maximum : Std.Usize) : Result Std.Usize := do
  loop
    (fun (degree1, maximum1) => decode.affine.MAX_PREFERRED_DEGREE_loop.body
      degree1 maximum1)
    (degree, maximum)

/-- [bulksketch::decode::affine::MAX_PREFERRED_DEGREE]
    Source: 'src/decode/affine.rs', lines 70:0-80:2 -/
@[global_simps, irreducible]
def decode.affine.MAX_PREFERRED_DEGREE : Result Std.Usize :=
  decode.affine.MAX_PREFERRED_DEGREE_loop 3#usize 0#usize

end bulksketch
