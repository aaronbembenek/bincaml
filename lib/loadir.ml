(** Loads a initial IR from the semi-concrete AST *)

open Lang
open Types
open Value
open Prog
open Expr
open Containers
module StringMap = Map.Make (String)

type load_st = {
  prog : Program.t;
  params_order :
    (string, (string * Var.t) list * (string * Var.t) list) Hashtbl.t;
}

let map_prog f l = { l with prog = f l.prog }

type textRange = (int * int) option [@@deriving show { with_path = false }, eq]

module BasilASTLoader = struct
  open BasilIR.AbsBasilIR

  type loaded_block =
    | LBlock of
        (string
        * Program.stmt list
        * [ `Return of Program.e list | `Goto of string list | `None ])

  let failure x = failwith "Undefined case." (* x discarded *)
  let stripquote s = String.sub s 1 (String.length s - 2)

  let rec transBVTYPE (x : bVTYPE) : BType.t =
    match x with
    | BVTYPE (_, string) ->
        let sz =
          String.split_on_char 'v' string |> function
          | h :: l :: _ -> int_of_string l
          | _ -> failwith "bad bv format"
        in
        Bitvector sz

  and transBIdent (x : bIdent) : string = match x with BIdent (_, id) -> id

  and transStr (x : str) : string =
    match x with Str string -> stripquote string

  and transProgram ?(name = "<module>") (x : moduleT) : load_st =
    let prog =
      { prog = Program.empty ~name (); params_order = Hashtbl.create 30 }
    in
    match x with
    | Module1 declarations ->
        List.fold_left transDeclaration prog declarations |> fun p ->
        List.fold_left transDefinition p declarations

  and transDeclaration prog (x : decl) : load_st =
    match x with
    | Decl_SharedMem (bident, type') ->
        map_prog
          (fun p ->
            Program.decl_glob p
              (Var.create
                 (unsafe_unsigil (`Global bident))
                 ~pure:false (transType type'));
            p)
          prog
    | Decl_UnsharedMem (bident, type') ->
        map_prog
          (fun p ->
            Program.decl_glob p
              (Var.create
                 (unsafe_unsigil (`Global bident))
                 ~pure:true (transType type'));
            p)
          prog
    | Decl_Var (bident, type') ->
        map_prog
          (fun p ->
            Program.decl_glob p
              (Var.create
                 (unsafe_unsigil (`Global bident))
                 ~pure:true (transType type'));
            p)
          prog
    | Decl_UninterpFun (attrDefList, glident, argtypes, rettype) -> prog
    | Decl_Fun (attrList, glident, params, rt, body) -> prog
    | Decl_Axiom _ -> prog
    | Decl_ProgEmpty _ -> prog
    | Decl_ProgWithSpec _ -> prog
    | Decl_Proc
        ( ProcIdent (id_pos, id),
          in_params,
          out_params,
          attrib,
          spec,
          ProcDef_Empty ) ->
        let formal_in_params_order = List.map param_to_formal in_params in
        let formal_out_params_order = List.map param_to_formal out_params in
        let _ = prog.prog.proc_names.fresh ~name:id () in
        Hashtbl.add prog.params_order id
          (formal_in_params_order, formal_out_params_order);
        prog
    | Decl_Proc
        ( ProcIdent (id_pos, id),
          in_params,
          out_params,
          attrs,
          spec_list,
          ProcDef_Some (bl, blocks, el) ) ->
        let proc_id = prog.prog.proc_names.fresh ~name:id () in
        let formal_in_params_order = List.map param_to_formal in_params in
        let formal_in_params = formal_in_params_order |> Params.M.of_list in
        let formal_out_params_order = List.map param_to_formal out_params in
        let formal_out_params = Params.M.of_list formal_out_params_order in
        Hashtbl.add prog.params_order id
          (formal_in_params_order, formal_out_params_order);
        let p =
          Procedure.create proc_id ~formal_in_params ~formal_out_params ()
        in
        let prog =
          map_prog
            (fun pr -> { pr with procs = ID.Map.add proc_id p pr.procs })
            prog
        in
        prog

  and transDefinition prog (x : decl) : load_st =
    match x with
    | Decl_Proc
        ( ProcIdent (id_pos, id),
          in_params,
          out_params,
          attrs,
          spec_list,
          ProcDef_Some (bl, blocks, el) ) ->
        let blocks = List.map (trans_block prog) blocks in
        let proc_id = prog.prog.proc_names.get_id id in
        let p = ID.Map.find proc_id prog.prog.procs in
        let open Procedure.Vert in
        let formal_out_params_order = List.map param_to_formal out_params in
        (* add blocks *)
        let blocks_id =
          List.map
            (function
              | LBlock (name, stmts, succ) ->
                  let stmts = stmts in
                  (name, Procedure.fresh_block p ~stmts ()))
            blocks
        in
        let block_label_id = StringMap.of_list blocks_id in
        Option.iter
          (fun (_, entry) -> Procedure.G.add_edge p.graph Entry (Begin entry))
          (List.head_opt blocks_id);

        (* add intraproc edges*)
        List.iter
          (function
            | LBlock (name, _, succ) -> (
                match succ with
                | `Goto tgts ->
                    let f = StringMap.find name block_label_id in
                    let succ =
                      List.map (fun c -> StringMap.find c block_label_id) tgts
                    in
                    Procedure.add_goto p ~from:f ~targets:succ
                | `Return exprs ->
                    let args =
                      List.combine formal_out_params_order exprs
                      |> List.map (function (name, var), expr -> (name, expr))
                      |> Params.M.of_list
                    in
                    let f = StringMap.find name block_label_id in
                    Procedure.add_return p ~from:f ~args
                | _ -> ()))
          blocks;
        prog
    | _ -> prog

  and transMapType (x : mapType) : BType.t =
    match x with MapType1 (t0, t1) -> Map (transType t0, transType t1)

  and transType (x : typeT) : BType.t =
    match x with
    | TypeIntType inttype -> Integer
    | TypeBoolType booltype -> Boolean
    | TypeMapType maptype -> transMapType maptype
    | TypeBVType (BVType1 bvtype) -> transBVTYPE bvtype

  and transIntVal (x : intVal) : PrimInt.t =
    match x with
    | IntVal_Hex (IntegerHex (_, ihex)) -> Z.of_string ihex
    | IntVal_Dec (IntegerDec (_, i)) -> Z.of_string i

  and transEndian (x : BasilIR.AbsBasilIR.endian) =
    match x with Endian_Little -> `Big | Endian_Big -> `Little

  and trans_stmt (p_st : load_st) (x : BasilIR.AbsBasilIR.stmtWithAttrib) =
    let stmt = match x with StmtWithAttrib1 (stmt, _) -> stmt in
    let open Stmt in
    match stmt with
    | Stmt_SingleAssign (Assignment1 (lvar, expr)) ->
        `Stmt (Instr_Assign [ (transLVar lvar, trans_expr expr) ])
    | Stmt_MultiAssign assigns ->
        `Stmt
          (Instr_Assign
             (assigns
             |> List.map (function Assignment1 (l, r) ->
                 (transLVar l, trans_expr r))))
    | Stmt_Load (lvar, endian, bident, expr, intval) ->
        let endian = transEndian endian in
        let mem =
          let n = unsafe_unsigil (`Global bident) in
          Option.get_exn_or ("memory undefined: " ^ n)
          @@ Var.Decls.find_opt p_st.prog.globals n
        in
        `Stmt
          (Instr_Load
             { lhs = transLVar lvar; mem; addr = trans_expr expr; endian })
    | Stmt_Store (endian, bident, addr, value, intval) ->
        let endian = transEndian endian in
        let mem =
          let n = unsafe_unsigil (`Global bident) in
          Option.get_exn_or ("memory undefined: " ^ n)
          @@ Var.Decls.find_opt p_st.prog.globals n
        in
        `Stmt
          (Instr_Store
             { mem; addr = trans_expr addr; value = trans_expr value; endian })
    | Stmt_DirectCall (calllvars, bident, exprs) ->
        let n = unsafe_unsigil (`Proc bident) in
        let procid = p_st.prog.proc_names.get_id n in
        let in_param, out_param = Hashtbl.find p_st.params_order n in
        let lhs = trans_call_lhs (List.map fst out_param) calllvars in
        let args =
          List.combine (List.map fst in_param) (List.map trans_expr exprs)
          |> Params.M.of_list
        in
        `Call (Instr_Call { lhs; procid; args })
    | Stmt_IndirectCall expr ->
        `Call (Instr_IndirectCall { target = trans_expr expr })
    | Stmt_Assume expr ->
        `Stmt (Instr_Assume { body = trans_expr expr; branch = false })
    | Stmt_Guard expr ->
        `Stmt (Instr_Assume { body = trans_expr expr; branch = true })
    | Stmt_Assert expr -> `Stmt (Instr_Assert { body = trans_expr expr })

  and trans_call_lhs (formal_out : string list) (x : lVars) : Params.lhs =
    match x with
    | LVars_Empty -> Params.M.empty
    | LVars_LocalList lvars ->
        List.combine formal_out (unpackLVars lvars) |> Params.M.of_list
    | LVars_List lvars ->
        List.combine formal_out @@ List.map transLVar lvars |> Params.M.of_list

  and unpackLVars lvs =
    List.map
      (function
        | LocalVar1 (i, t) ->
            Var.create (unsafe_unsigil (`Local i)) (transType t))
      lvs

  and trans_jump (x : BasilIR.AbsBasilIR.jumpWithAttrib) =
    let jump = match x with JumpWithAttrib1 (jump, _) -> jump in
    match jump with
    | Jump_GoTo bidents ->
        let get_id = function BlockIdent (pos, g) -> g in
        `Goto (List.map get_id bidents)
    | Jump_Unreachable -> `None
    | Jump_Return exprs -> `Return (List.map trans_expr exprs)

  and transLVar (x : BasilIR.AbsBasilIR.lVar) : Var.t =
    match x with
    | LVar_Local (LocalVar1 (bident, type')) ->
        Var.create (unsafe_unsigil (`Local bident)) (transType type')
    | LVar_Global (GlobalVar1 (bident, type')) ->
        Var.create (unsafe_unsigil (`Global bident)) (transType type')

  and list_begin_end_to_textrange beginlist endlist : textRange =
    let beg = match beginlist with BeginList ((i, j), l) -> i in
    let ed = match endlist with EndList ((i, j), l) -> j in
    Some (beg, ed)

  and rec_begin_end_to_textrange beginlist endlist : textRange =
    let beg = match beginlist with BeginRec ((i, j), l) -> i in
    let ed = match endlist with EndRec ((i, j), l) -> j in
    Some (beg, ed)

  and trans_block (prog : load_st) (x : BasilIR.AbsBasilIR.block) =
    match x with
    | Block1
        ( BlockIdent (text_range, name),
          addrattr,
          beginlist,
          statements,
          jump,
          endlist ) ->
        let stmts =
          List.map (trans_stmt prog) statements
          |> List.map (function `Call c -> c | `Stmt c -> c)
        in
        let succ = trans_jump jump in
        LBlock (name, stmts, succ)

  and param_to_lvar (pp : params) : Var.t =
    match pp with
    | Params1 (LocalIdent (pos, id), t) -> Var.create id (transType t)

  and param_to_formal (pp : params) : string * Var.t =
    match pp with
    | Params1 (LocalIdent (pos, id), t) -> (id, Var.create id (transType t))

  and unsafe_unsigil g : string =
    match g with
    | `Global (GlobalIdent (pos, g)) -> g
    | `Local (LocalIdent (pos, g)) -> g
    | `Proc (ProcIdent (pos, g)) -> g
    | `Block (BlockIdent (pos, g)) -> g

  and trans_expr (x : BasilIR.AbsBasilIR.expr) : BasilExpr.t =
    let open Ops in
    match x with
    | Expr_Global (GlobalVar1 (g, type')) ->
        BasilExpr.rvar
        @@ Var.create (unsafe_unsigil (`Global g)) (transType type')
    | Expr_Local (LocalVar1 (g, type')) ->
        BasilExpr.rvar
        @@ Var.create (unsafe_unsigil (`Local g)) (transType type')
    | Expr_Assoc (binop, rs) -> (
        match transBoolBinOp binop with
        | #AllOps.intrin as op ->
            BasilExpr.applyintrin ~op (List.map trans_expr rs)
        | _ -> failwith "non-associative operator")
    | Expr_Binary (binop, expr0, expr) -> (
        let op = transBinOp binop in
        let e1 = trans_expr expr0 in
        let e2 = trans_expr expr in
        match op with
        | #AllOps.binary as op -> BasilExpr.binexp ~op e1 e2
        | #AllOps.intrin as op -> BasilExpr.applyintrin ~op [ e1; e2 ]
        | `BVUGT -> BasilExpr.boolnot (BasilExpr.binexp ~op:`BVULE e1 e2)
        | `BVUGE -> BasilExpr.boolnot (BasilExpr.binexp ~op:`BVULT e1 e2)
        | `BVSGT -> BasilExpr.boolnot (BasilExpr.binexp ~op:`BVSLE e1 e2)
        | `BVSGE -> BasilExpr.boolnot (BasilExpr.binexp ~op:`BVSLT e1 e2)
        | `BVXNOR -> BasilExpr.boolnot (BasilExpr.binexp ~op:`BVXOR e1 e2)
        | `BVNOR -> BasilExpr.boolnot (BasilExpr.binexp ~op:`BVOR e1 e2)
        | `BVCOMP ->
            BasilExpr.unexp ~op:`BOOL2BV1 (BasilExpr.binexp ~op:`EQ e1 e2)
        | `INTGE -> BasilExpr.boolnot (BasilExpr.binexp ~op:`INTLT e1 e2)
        | `INTGT -> BasilExpr.boolnot (BasilExpr.binexp ~op:`INTLE e1 e2))
    | Expr_Unary (unop, expr) ->
        BasilExpr.unexp ~op:(transUnOp unop) (trans_expr expr)
    | Expr_ZeroExtend (intval, expr) ->
        BasilExpr.zero_extend
          ~n_prefix_bits:(Z.to_int @@ transIntVal intval)
          (trans_expr expr)
    | Expr_SignExtend (intval, expr) ->
        BasilExpr.sign_extend
          ~n_prefix_bits:(Z.to_int @@ transIntVal intval)
          (trans_expr expr)
    | Expr_Extract (ival0, intval, expr) ->
        BasilExpr.extract
          ~hi_incl:(transIntVal ival0 |> Z.to_int)
          ~lo_excl:(transIntVal intval |> Z.to_int)
          (trans_expr expr)
    | Expr_Concat (expr0, expr) ->
        BasilExpr.concat (trans_expr expr0) (trans_expr expr)
    | Expr_Literal (Value_BV (BVVal1 (intval, BVType1 bvtype))) ->
        BasilExpr.bvconst
          (match transBVTYPE bvtype with
          | Bitvector width -> PrimQFBV.create ~width (transIntVal intval)
          | _ -> failwith "unreachable")
    | Expr_Literal (Value_Int intval) -> BasilExpr.intconst (transIntVal intval)
    | Expr_Literal Value_True -> BasilExpr.boolconst true
    | Expr_Literal Value_False -> BasilExpr.boolconst false
    | Expr_Old e -> BasilExpr.unexp ~op:`Old (trans_expr e)
    | Expr_Forall (LambdaDef1 (lv, _, e)) ->
        BasilExpr.forall
          ~bound:(List.map BasilExpr.rvar @@ unpackLVars lv)
          (trans_expr e)
    | Expr_Exists (LambdaDef1 (lv, _, e)) ->
        BasilExpr.exists
          ~bound:(List.map BasilExpr.rvar @@ unpackLVars lv)
          (trans_expr e)
    | Expr_FunctionOp (gi, args) ->
        BasilExpr.apply_fun
          ~name:(unsafe_unsigil (`Global gi))
          (List.map trans_expr args)

  and transBinOp (x : BasilIR.AbsBasilIR.binOp) =
    match x with
    | BinOpBVBinOp bvbinop -> transBVBinOp bvbinop
    | BinOpBVLogicalBinOp bvlogicalbinop -> transBVLogicalBinOp bvlogicalbinop
    | BinOpBoolBinOp boolbinop -> transBoolBinOp boolbinop
    | BinOpIntLogicalBinOp intlogicalbinop ->
        transIntLogicalBinOp intlogicalbinop
    | BinOpIntBinOp intbinop -> transIntBinOp intbinop
    | BinOpEqOp equop -> transEqOp equop

  and transUnOp (x : BasilIR.AbsBasilIR.unOp) =
    match x with
    | UnOpBVUnOp bvunop -> transBVUnOp bvunop
    | UnOp_boolnot -> `BoolNOT
    | UnOp_intneg -> `INTNEG
    | UnOp_booltobv1 -> `BOOL2BV1

  and transBVUnOp (x : bVUnOp) =
    match x with BVUnOp_bvnot -> `BVNOT | BVUnOp_bvneg -> `BVNEG

  and transBVBinOp (x : BasilIR.AbsBasilIR.bVBinOp) =
    match x with
    | BVBinOp_bvand -> `BVAND
    | BVBinOp_bvor -> `BVOR
    | BVBinOp_bvadd -> `BVADD
    | BVBinOp_bvmul -> `BVMUL
    | BVBinOp_bvudiv -> `BVUDIV
    | BVBinOp_bvurem -> `BVUREM
    | BVBinOp_bvshl -> `BVSHL
    | BVBinOp_bvlshr -> `BVLSHR
    | BVBinOp_bvnand -> `BVNAND
    | BVBinOp_bvxor -> `BVXOR
    | BVBinOp_bvcomp -> `BVCOMP
    | BVBinOp_bvsub -> `BVSUB
    | BVBinOp_bvsdiv -> `BVSDIV
    | BVBinOp_bvsrem -> `BVSREM
    | BVBinOp_bvsmod -> `BVSMOD
    | BVBinOp_bvashr -> `BVASHR
    | BVBinOp_bvnor -> `BVNOR
    | BVBinOp_bvxnor -> `BVXNOR

  and transBVLogicalBinOp (x : bVLogicalBinOp) =
    match x with
    | BVLogicalBinOp_bvule -> `BVULE
    | BVLogicalBinOp_bvult -> `BVULT
    | BVLogicalBinOp_bvslt -> `BVSLT
    | BVLogicalBinOp_bvsle -> `BVSLE
    | BVLogicalBinOp_bvugt -> `BVUGT
    | BVLogicalBinOp_bvuge -> `BVUGE
    | BVLogicalBinOp_bvsgt -> `BVSGT
    | BVLogicalBinOp_bvsge -> `BVSGE

  and transEqOp (x : eqOp) = match x with EqOp_eq -> `EQ | EqOp_neq -> `NEQ

  and transIntBinOp (x : intBinOp) =
    match x with
    | IntBinOp_intadd -> `INTADD
    | IntBinOp_intmul -> `INTMUL
    | IntBinOp_intsub -> `INTSUB
    | IntBinOp_intdiv -> `INTDIV
    | IntBinOp_intmod -> `INTMOD

  and transIntLogicalBinOp (x : intLogicalBinOp) =
    match x with
    | IntLogicalBinOp_intlt -> `INTLT
    | IntLogicalBinOp_intle -> `INTLE
    | IntLogicalBinOp_intgt -> `INTGT
    | IntLogicalBinOp_intge -> `INTGE

  and transBoolBinOp (x : boolBinOp) =
    match x with
    | BoolBinOp_booland -> `AND
    | BoolBinOp_boolor -> `OR
    | BoolBinOp_boolimplies -> `IMPLIES
end

let ast_of_concrete_ast m = BasilASTLoader.transProgram m

let ast_of_channel fname c =
  let m = Basilloader.Cast_loader.concrete_ast_of_channel c in
  BasilASTLoader.transProgram ~name:fname m

let ast_of_fname fname = IO.with_in fname (fun c -> ast_of_channel fname c)
