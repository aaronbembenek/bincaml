open Expr
open Value
open Ops
open Containers

let eval_expr (e : Ops.AllOps.const option BasilExpr.abstract_expr) =
  let open AbstractExpr in
  let open Value in
  let bool e = Some (`Bool e) in
  let bv e = `Bitvector e in
  let z e = Some (`Integer e) in

  let get_bv = function Some (`Bitvector b) -> Some b | _ -> None in
  let get_bool = function Some (`Bool b) -> Some b | _ -> None in
  let get_int = function Some (`Integer b) -> Some b | _ -> None in

  let all_args f args =
    let e_args = List.filter_map f args in
    if List.length e_args = List.length args then Some e_args else None
  in

  let open Option.Infix in
  match e with
  | RVar _ -> None
  | Constant v -> Some v
  | BinaryExpr (`EQ, a, b) ->
      let* a = a in
      let* b = b in
      bool (AllOps.eval_equal a b)
  | BinaryExpr (`NEQ, a, b) ->
      let* a = a in
      let* b = b in
      bool (not @@ AllOps.eval_equal a b)
  | UnaryExpr ((#BVOps.unary_unif as op), b) ->
      get_bv b >|= BVOps.eval_unary_unif op >|= bv
  | UnaryExpr ((#BVOps.unary_bool as op), b) ->
      get_bool b >|= BVOps.eval_unary_bool op >|= bv
  | BinaryExpr ((#BVOps.binary_unif as op), a, b) ->
      let* a = get_bv a in
      let* b = get_bv b in
      Some (bv (BVOps.eval_binary_unif op a b))
  | BinaryExpr ((#BVOps.binary_pred as op), a, b) ->
      let* a = get_bv a in
      let* b = get_bv b in
      bool (BVOps.eval_binary_pred op a b)
  | ApplyIntrin ((#BVOps.intrin as op), args) ->
      let* args = all_args get_bv args in
      Some (bv (BVOps.eval_intrin op args))
  | UnaryExpr (`NOT, b) -> get_bv b >|= PrimQFBV.bitnot >|= bv
  | UnaryExpr (`Forall, b) -> None
  | UnaryExpr (`Old, b) -> None
  | UnaryExpr (`Exists, b) -> None
  | UnaryExpr ((#IntOps.unary as op), b) ->
      get_int b >|= IntOps.eval_unary op >|= fun b -> `Integer b
  | BinaryExpr ((#IntOps.binary_unif as op), a, b) ->
      let* a = get_int a in
      let* b = get_int b in
      z (IntOps.eval_binary_unif op a b)
  | BinaryExpr ((#IntOps.binary_pred as op), a, b) ->
      let* a = get_int a in
      let* b = get_int b in
      bool (IntOps.eval_binary_pred op a b)
  | BinaryExpr (`IMPLIES, a, b) ->
      let* a = get_bool a in
      let* b = get_bool b in
      bool (b || not a)
  | ApplyIntrin ((#LogicalOps.intrin as op), args) ->
      let* args = all_args get_bool args in
      bool @@ LogicalOps.eval_intrin op args
  | ApplyFun _ -> None
  | Binding _ -> None
