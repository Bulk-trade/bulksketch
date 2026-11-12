open Aeneas
open Types
open Values

let _, fresh_region = RegionId.fresh_stateful_generator ()
let owned = RVar (Free (fresh_region ()))
let outside = RVar (Free (fresh_region ()))
let unit_ty = TypesUtils.mk_unit_ty
let shared = TypesUtils.mk_tuple_ty [TRef (owned, unit_ty, RShared); TRef (outside, unit_ty, RMut)]
let mutable_owned = TRef (owned, unit_ty, RMut)
let empty = ValuesUtils.mk_etuple ~borrow_proj:true []
let abs_id = AbsId.zero
let loop_id = LoopId.zero
let sv_id = SymbolicValueId.zero

let make_abs ~loan_type ~consumed_type ~given_back_type ~child_is_active =
  let proj : symbolic_proj = { sv_id; proj_ty = shared } in
  let child =
    if child_is_active then AProjLoans { proj; consumed = []; borrows = [] }
    else AEndedProjLoans { proj = sv_id;
      consumed = [({ sv_id; proj_ty = consumed_type }, AEmpty)]; borrows = [] }
  in
  let parent = AEndedProjBorrows {
    mvalues = { consumed = sv_id; given_back = { sv_id; sv_ty = given_back_type } };
    loans = [({ sv_id; proj_ty = loan_type }, child)] }
  in
  { abs_id; kind = Loop loop_id; can_end = true; parents = AbsId.Set.empty;
    regions = { owned = RegionSet.singleton owned };
    ended_subabs = AbsLevelSet.singleton 1;
    avalues = [ { value = ASymbolic (PNone, parent); ty = shared };
                { value = ASymbolic (PNone, AProjLoans { proj; consumed = []; borrows = [] }); ty = shared } ];
    cont = Some { output = Some empty;
                  input = Some { value = EApp (ELoop (abs_id, loop_id), [[]]); ty = unit_ty } } }

let check name expected ?(ignored=true) ?(has_continuation=false) ?(level=1) abs =
  let actual = SymbolicToPureExpressions.can_erase_shared_loop_end TypeDeclId.Map.empty
    ~ignored ~has_continuation abs level in
  if actual <> expected then failwith (name ^ " has the wrong erasure result");
  Printf.printf "PASS %s\n%!" name

let () =
  Config.sanity_checks := true;
  let safe = make_abs ~loan_type:shared ~consumed_type:shared ~given_back_type:shared ~child_is_active:false in
  check "shared-owned-region" true safe;
  check "mutable-loan-payload" false
    (make_abs ~loan_type:mutable_owned ~consumed_type:shared ~given_back_type:shared ~child_is_active:false);
  check "mutable-consumed-payload" false
    (make_abs ~loan_type:shared ~consumed_type:mutable_owned ~given_back_type:shared ~child_is_active:false);
  check "mutable-given-back-payload" false
    (make_abs ~loan_type:shared ~consumed_type:shared ~given_back_type:mutable_owned ~child_is_active:false);
  check "active-child-loan" false
    (make_abs ~loan_type:shared ~consumed_type:shared ~given_back_type:shared ~child_is_active:true);
  check "registered-continuation" false ~has_continuation:true safe;
  check "unregistered-erasure" false ~ignored:false safe;
  check "level-zero" false ~level:0 safe;
  check "level-two" false ~level:2 safe;
  check "join-ending" false { safe with kind = Join };
  check "unended-level" false { safe with ended_subabs = AbsLevelSet.empty };
  check "data-continuation" false
    { safe with cont = Some { output = Some empty;
        input = Some { value = EApp (ELoop (abs_id, loop_id), [[empty]]); ty = unit_ty } } };
  Config.sanity_checks := false;
  check "unchecked" false safe
