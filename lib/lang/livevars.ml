open Containers
open Expr
open Prog
open Types
module V = BasilExpr.VarSet
module B = Map.Make (Var)

let show_v b =
  V.to_list b
  |> List.map (fun v -> Printf.sprintf "%s" (Var.name v))
  |> String.concat ", "

let assigned_stmt (init : V.t) s : V.t =
  let f_lvar a v = V.add v a in
  Stmt.iter_lvar s |> Iter.fold f_lvar init

let free_vars_stmt (init : V.t) (s : (Var.t, Var.t, BasilExpr.t) Stmt.t) : V.t =
  let f_expr a v = V.union (BasilExpr.free_vars v) a in
  Stmt.iter_rexpr s |> Iter.fold f_expr init

let tf_block (init : V.t) (b : (Var.t, BasilExpr.t) Block.t) =
  let tf_stmt init s =
    let assigns = V.diff init (assigned_stmt V.empty s) in
    free_vars_stmt assigns s
  in
  Block.fold_stmt_backwards ~f:tf_stmt ~phi:(fun f _ -> f) ~init b

module G = Procedure.G

module LV =
  Graph.Fixpoint.Make
    (G)
    (struct
      type vertex = G.E.vertex
      type edge = G.E.t
      type g = G.t
      type data = V.t

      let direction = Graph.Fixpoint.Backward
      let equal = V.equal
      let join = V.union

      let analyze (e : edge) d =
        match G.E.label e with Block b -> tf_block d b | _ -> d
    end)

let run (p : Procedure.t) = LV.analyze (function e -> V.empty) p.graph
let label (r : G.vertex -> V.t) (v : G.vertex) = show_v (r v)
let print_g res = Viscfg.dot_labels (fun v -> Some (label res v))

let print_live_vars_dot fmt p =
  let r = run p in
  let (module M : Viscfg.ProcPrinter) =
    Viscfg.dot_labels (fun v -> Some (label r v))
  in
  M.fprint_graph fmt p.graph

let%expect_test _ =
  let open BasilExpr in
  let v1 = Var.create "v1" (BType.bv 0x1) in
  let v2 = Var.create "v2" (BType.bv 0x1) in
  let v3 = Var.create "v3" (BType.bv 0x1) in

  let e1 =
    BasilExpr.forall
      ~bound:[ rvar v2 ]
      (applyintrin ~op:`AND [ rvar v1; rvar v2; rvar v3 ])
  in
  let exp = BasilExpr.forall ~bound:[ rvar v1 ] (binexp ~op:`EQ (rvar v2) e1) in
  print_endline (to_string exp);
  let sub v = Some (bvconst (Value.PrimQFBV.of_int ~width:5 150)) in
  let e2 = BasilExpr.substitute sub exp in
  print_endline (to_string e2);
  [%expect
    {|
    forall(v1:bv1 :: eq(v2:bv1, forall(v2:bv1 :: and(v1:bv1, v2:bv1, v3:bv1))))
    forall(v1:bv1 :: eq(0x16:bv5, forall(v2:bv1 :: and(v1:bv1, v2:bv1, 0x16:bv5)))) |}]
