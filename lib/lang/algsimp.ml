(** Basic intra-expression algebraic simplifications *)

open Bincaml_util.Common
open Expr
open Ops

let normalise_bool
    (e : BasilExpr.t BasilExpr.abstract_expr BasilExpr.abstract_expr) =
  let open AbstractExpr in
  let open BasilExpr in
  let open Bitvec in
  match e with
  | BinaryExpr (`IMPLIES, a, b) ->
      Some (BasilExpr.applyintrin ~op:`OR [ fix a; BasilExpr.boolnot (fix b) ])
  | UnaryExpr (`BoolNOT, UnaryExpr (`BoolNOT, b)) -> Some b
  | UnaryExpr (`BoolNOT, ApplyIntrin (`AND, b)) ->
      Some (BasilExpr.applyintrin ~op:`OR (List.map BasilExpr.boolnot b))
  | UnaryExpr (`BoolNOT, ApplyIntrin (`OR, b)) ->
      Some (BasilExpr.applyintrin ~op:`AND (List.map BasilExpr.boolnot b))
  | _ -> None

let algebraic_simplifications
    (e :
      (BasilExpr.t BasilExpr.abstract_expr * Types.t) BasilExpr.abstract_expr) =
  let open AbstractExpr in
  let open BasilExpr in
  let open Bitvec in
  let keep a = Some (fix (fst a)) in
  match e with
  | ApplyIntrin (`BVConcat, (ApplyIntrin (`BVConcat, al), _) :: tl) ->
      Some
        (fix (ApplyIntrin (`BVConcat, al @ List.map (fun i -> fix (fst i)) tl)))
  | BinaryExpr (`BVADD, a, (Constant (`Bitvector i), _)) when is_zero i ->
      keep a
  | BinaryExpr (`BVSUB, a, (Constant (`Bitvector i), _)) when is_zero i ->
      keep a
  | BinaryExpr (`BVMUL, a, (Constant (`Bitvector i), _))
    when equal i @@ of_int ~size:(size i) 1 ->
      keep a
  | BinaryExpr (`BVAND, a, (Constant (`Bitvector i), _)) when is_zero i ->
      Some (bvconst (zero ~size:(size i)))
  | BinaryExpr (`BVAND, a, (Constant (`Bitvector i), _))
    when equal i (ones ~size:(size i)) ->
      keep a
  | BinaryExpr (`BVOR, a, (Constant (`Bitvector i), _))
    when equal i (ones ~size:(size i)) ->
      Some (bvconst @@ ones ~size:(size i))
  | BinaryExpr (`BVOR, a, (Constant (`Bitvector i), _)) when is_zero i -> keep a
  | UnaryExpr (`ZeroExtend 0, a) -> keep a
  | UnaryExpr (`SignExtend 0, a) -> keep a
  | UnaryExpr (`Extract (hi, 0), (a, Bitvector sz)) when hi = sz -> Some (fix a)
  | UnaryExpr (`BVNOT, (UnaryExpr (`BVNOT, a), _)) -> Some a
  | UnaryExpr (`BoolNOT, (UnaryExpr (`BoolNOT, a), _)) -> Some a
  | _ -> None

let alg_simp_rewriter e =
  let partial_eval_expr e =
    BasilExpr.rewrite ~rw_fun:Expr_eval.partial_eval_alg e
  in
  BasilExpr.rewrite_typed_two algebraic_simplifications (partial_eval_expr e)

let normalise e =
  let e = alg_simp_rewriter e in
  BasilExpr.rewrite_two normalise_bool e

let%expect_test "normalise" =
  let e =
    BasilExpr.boolnot @@ BasilExpr.boolnot @@ BasilExpr.boolnot
    @@ BasilExpr.applyintrin ~op:`AND
         [
           BasilExpr.boolnot
             (BasilExpr.boolnot (BasilExpr.rvar (Var.create "b" Boolean)));
           BasilExpr.rvar (Var.create "a" Boolean);
         ]
  in
  print_endline (BasilExpr.to_string e);
  let e = normalise e in
  print_endline (BasilExpr.to_string e);
  [%expect
    {|
    boolnot(boolnot(boolnot(booland(boolnot(boolnot(b:bool)), a:bool))))
    boolor(boolnot(b:bool), boolnot(a:bool))
    |}]
