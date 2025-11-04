open Value
open Common
open Types
open Expr
open Containers

module Params = struct
  module M = Map.Make (String) [@@deriving show]

  type formal = Var.t M.t [@@deriving eq, ord]
  type actual = BasilExpr.t M.t [@@deriving eq, ord]
  type lhs = Var.t M.t [@@deriving eq, ord]

  let show_actual a =
    M.to_list a
    |> List.map (function k, v ->
        Printf.sprintf "%s -> %s" k (BasilExpr.to_string v))
    |> String.concat ", "
    |> fun x -> "(" ^ x ^ ")"

  let pp_actual fmt a = Format.pp_print_string fmt (show_actual a)

  let show_formal (a : formal) =
    M.to_list a
    |> List.map (function k, v -> Printf.sprintf "%s -> %s" k (Var.to_string v))
    |> String.concat ", "
    |> fun x -> "(" ^ x ^ ")"

  let pp_formal fmt a = Format.pp_print_string fmt (show_formal a)

  let show_lhs (a : lhs) =
    M.to_list a
    |> List.map (function k, v -> Printf.sprintf "%s <- %s" (Var.to_string v) k)
    |> String.concat ", "
    |> fun x -> "(" ^ x ^ ")"

  let pp_lhs fmt a = Format.pp_print_string fmt (show_lhs a)
end

module Stmt = struct
  type endian = [ `Big | `Little ] [@@deriving eq, ord]
  type ident = string

  let show_endian = function `Big -> "be" | `Little -> "le"
  let pp_endian fmt e = Format.pp_print_string fmt (show_endian e)

  type ('lvar, 'var, 'expr) t =
    | Instr_Assign of ('lvar * 'expr) list
        (** simultaneous assignment of expr snd to lvar fst*)
    | Instr_Assert of { body : 'expr }  (** assertions *)
    | Instr_Assume of { body : 'expr; branch : bool }
        (** assumption; or branch guard *)
    | Instr_Load of {
        lhs : 'lvar;
        mem : 'var;
        addr : 'expr;
        cells : int;
        endian : endian;
      }
        (** a load from memory index [addr] up to of [addr] + [cells] (byte
            swapped depending on endiannesss, and concatenated and stored into
            [lhs]*)
    | Instr_Store of {
        mem : 'var;
        addr : 'expr;
        value : 'expr;
        cells : int;
        endian : endian;
      }
        (** a store into memory indexes [addr] up to of [addr] + [cells] (of
            [value] byte swapped depending on endiannesss*)
    | Instr_IntrinCall of {
        lhs : 'lvar Params.M.t;
        name : string;
        args : 'expr Params.M.t;
      }  (** effectful operation calling a named intrinsic*)
    | Instr_Return of { args : 'expr Params.M.t }
        (** return to caller with [args] as return values (bound to the formal
            out parameters of this procedure)*)
    | Instr_Call of {
        lhs : 'lvar Params.M.t;
        procid : ID.t;
        args : 'expr Params.M.t;
      }
        (** call a procedure with the args, assigning its return parameters to
            lhs *)
    | Instr_IndirectCall of { target : 'expr }
        (** call to the address of a procedure or block stored in [target], due
            to its nature local behaviour is not captured and hence will have
            incorrect semantics unless all behaviour in the IR is encoded as
            global effects *)
  [@@deriving eq, ord, map]

  let map ~f_lvar ~f_expr ~f_rvar e = map f_lvar f_rvar f_expr e

  (** return an iterator over any memory field in the statement (read or
      written) *)
  let iter_mem_access stmt =
    match stmt with
    | Instr_Load { lhs; mem; addr; endian } -> Iter.singleton mem
    | Instr_Store { mem; addr; value; endian } -> Iter.singleton mem
    | _ -> Iter.empty

  (** return an iterator containing the memory written to by the statement *)
  let iter_mem_store stmt =
    match stmt with
    | Instr_Store { mem; addr; value; endian } -> Iter.singleton mem
    | _ -> Iter.empty

  (** get an iterator over the expresions in the RHS of the statement *)
  let iter_rexpr stmt =
    let open Iter.Infix in
    match stmt with
    | Instr_Assign ls -> List.to_iter ls >|= snd
    | Instr_Assert { body } -> Iter.singleton body
    | Instr_Assume { body } -> Iter.singleton body
    | Instr_Load { lhs; mem; addr; endian } -> Iter.singleton addr
    | Instr_Store { mem; addr; value; endian } ->
        Iter.singleton value <+> Iter.singleton addr
    | Instr_IntrinCall { lhs; name; args } -> Params.M.to_iter args >|= snd
    | Instr_IndirectCall { target } -> Iter.singleton target
    | Instr_Call { lhs; procid; args } -> Params.M.to_iter args >|= snd
    | Instr_Return { args } -> Params.M.to_iter args >|= snd

  (** get an iterator over the variables in the LHS of the statement *)
  let iter_lvar stmt =
    let open Iter.Infix in
    match stmt with
    | Instr_Assign ls -> List.to_iter ls >|= fst
    | Instr_Assert { body } -> Iter.empty
    | Instr_Assume { body } -> Iter.empty
    | Instr_Load { lhs; mem; addr; endian } -> Iter.singleton lhs
    | Instr_Store { mem; addr; value; endian } -> Iter.singleton mem
    | Instr_IntrinCall { lhs; name; args } -> Params.M.to_iter lhs >|= snd
    | Instr_IndirectCall { target } -> Iter.empty
    | Instr_Call { lhs; procid; args } -> Params.M.to_iter lhs >|= snd
    | Instr_Return { args } -> Iter.empty

  (** Get pretty-printer for il format*)
  let pretty show_lvar show_var show_expr s =
    let open Containers_pp in
    let open Containers_pp.Infix in
    let r_param_list l =
      if Params.M.is_empty l then text "()"
      else
        let l =
          Params.M.to_list l |> List.map (fun (i, t) -> text i ^ text "=" ^ t)
        in
        bracket "(" (nest 2 (fill (text "," ^ newline_or_spaces 1) l)) ")"
    in
    let l_param_list l =
      if Params.M.is_empty l then text ""
      else
        let l =
          Params.M.to_list l |> List.map (fun (i, t) -> t ^ text "=" ^ text i)
        in
        bracket "(" (nest 2 (fill (text "," ^ newline_or_spaces 1) l)) ") := "
    in
    let show_lvar v = text @@ show_lvar v in
    let show_var v = text @@ show_var v in
    let show_expr e = text @@ show_expr e in
    let e = map ~f_lvar:show_lvar ~f_expr:show_expr ~f_rvar:show_var s in
    match e with
    | Instr_Assign ls ->
        let ls = List.map (function lhs, rhs -> lhs ^ text " := " ^ rhs) ls in
        let b = fill (text " ,") ls in
        if List.length ls > 1 then bracket "(" b ")" else b
    | Instr_Assert { body } -> text "assert " ^ body
    | Instr_Assume { body; branch = false } -> text "assume " ^ body
    | Instr_Assume { body; branch = true } -> text "guard " ^ body
    | Instr_Load { lhs; mem; addr; cells; endian } ->
        lhs ^ text " := " ^ text "load "
        ^ text (show_endian endian)
        ^ text " " ^ mem ^ text " " ^ addr ^ text " " ^ int cells
    | Instr_Store { mem; addr; value; cells; endian } ->
        text "store "
        ^ text (show_endian endian)
        ^ text " " ^ mem ^ text " " ^ addr ^ text " " ^ value ^ text " "
        ^ int cells
    | Instr_IntrinCall { lhs; name; args } when Params.M.cardinal lhs = 0 ->
        append_l ~sep:nil [ text "call "; text name; r_param_list args ]
    | Instr_IntrinCall { lhs; name; args } ->
        append_l ~sep:nil
          [
            l_param_list lhs;
            newline ^ text "call ";
            text name;
            r_param_list args;
          ]
    | Instr_Call { lhs; procid; args } ->
        let n = ID.to_string procid in
        append_l ~sep:nil
          [
            l_param_list lhs; newline ^ text "call "; text n; r_param_list args;
          ]
    | Instr_Return { args } -> text "return " ^ r_param_list args
    | Instr_IndirectCall { target } -> text "indirect_call " ^ target

  (** Pretty print to il format*)
  let to_string ?width show_lvar show_var show_expr
      (s : (Var.t, Var.t, BasilExpr.t) t) =
    let width = Option.get_or ~default:80 width in
    let d = pretty show_lvar show_var show_expr s in
    Containers_pp.Pretty.to_string ~width d
end

module Block = struct
  type 'var phi = { lhs : 'var; rhs : (ID.t * 'var) list }
  [@@deriving eq, ord, show]
  (** a phi node representing the join of incoming edges assigned to a lhs
      variable*)

  module V = struct
    type 'a t = 'a Vector.ro_vector

    let equal e a b = Vector.equal e a b
    let compare e a b = Vector.compare e a b
  end

  type ('v, 'e) t = {
    phis : 'v phi list;
        (** List of phi nodes simultaneously assigning each input variable *)
    stmts : ('v, 'v, 'e) Stmt.t V.t;  (** statement list *)
  }
  [@@deriving eq, ord]

  let pretty_phi show_var v =
    let open Containers_pp in
    let open Containers_pp.Infix in
    let lhs = text (show_var v.lhs) in
    let rhs =
      List.map
        (function
          | bid, v ->
              (text @@ ID.to_string bid) ^ text " -> " ^ text (show_var v))
        v.rhs
    in
    lhs ^ text " := phi" ^ (bracket "(" (fill (text ", ") rhs)) ")"

  let pretty show_lvar show_var show_expr ?(terminator = []) ?block_id b =
    let open Containers_pp in
    let open Containers_pp.Infix in
    let phi =
      match b.phis with
      | [] -> []
      | o ->
          let phi = List.map (pretty_phi show_var) o in
          [ bracket "(" (fill (text ",") phi) ")" ]
    in
    let stmts =
      Vector.to_list b.stmts
      |> List.map (Stmt.pretty show_lvar show_var show_expr)
    in
    let stmts = phi @ stmts @ terminator in
    let stmts =
      bracket "["
        (nest 2 @@ newline ^ append_l ~sep:(text ";" ^ newline) stmts)
        "]"
    in
    let name =
      Option.map
        (fun id -> text "block " ^ text (ID.to_string id) ^ text " ")
        block_id
    in
    let name = Option.get_or ~default:nil name in
    name ^ stmts

  let to_string b =
    let b = pretty Var.to_string Var.to_string BasilExpr.to_string b in
    Containers_pp.Pretty.to_string ~width:80 b

  let stmts_iter b = Vector.to_iter b.stmts

  let fold_forwards ~(phi : 'acc -> 'v phi list -> 'acc)
      ~(f : 'acc -> ('v, 'v, 'e) Stmt.t -> 'acc) (i : 'a) (b : ('v, 'e) t) :
      'acc =
    Iter.fold f (phi i b.phis) (Vector.to_iter b.stmts)

  let foldi_backwards ~(f : 'acc -> int * ('v, 'v, 'e) Stmt.t -> 'acc)
      ~(phi : 'acc -> 'v phi list -> 'acc) ~(init : 'a) (b : ('v, 'e) t) : 'acc
      =
    Iter.fold f init
      (Vector.to_iter_rev (Vector.mapi (fun i b -> (i, b)) b.stmts))
    |> fun e -> phi e b.phis

  let fold_backwards ~(f : 'acc -> ('v, 'v, 'e) Stmt.t -> 'acc)
      ~(phi : 'acc -> 'v phi list -> 'acc) ~(init : 'a) (b : ('v, 'e) t) : 'acc
      =
    Iter.fold f init (Vector.to_iter_rev b.stmts) |> fun e -> phi e b.phis
end

module Procedure = struct
  type ident = Proc of int [@@unboxed]

  module Vert = struct
    type t = Begin of ID.t | End of ID.t | Entry | Return | Exit
    [@@deriving show { with_path = false }, eq, ord]

    let hash (v : t) =
      let h = Hash.pair Hash.int Hash.int in
      Hash.map
        (function
          | Entry -> (1, 1)
          | Return -> (3, 1)
          | Exit -> (5, 1)
          | Begin i -> (31, ID.hash i)
          | End i -> (37, ID.hash i))
        h v

    let block_id_string = function
      | Begin i -> ID.to_string i
      | End i -> ID.to_string i
      | Entry -> "proc_entry"
      | Return -> "return"
      | Exit -> "exit"
  end

  module Edge = struct
    type block = (Var.t, BasilExpr.t) Block.t [@@deriving eq, ord]
    type t = Block of block | Jump [@@deriving eq, ord]

    let show = function Block b -> Block.to_string b | Jump -> "goto"
    let to_string = function Block b -> Block.to_string b | Jump -> "goto"
    let default = Jump
  end

  module Loc = Int

  module G = struct
    include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Vert) (Edge)
  end

  type ('v, 'e) proc_spec = {
    requires : BasilExpr.t list;
    ensures : BasilExpr.t list;
    captures_globs : 'v list;
    modifies_globs : 'v list;
  }

  type ('v, 'e) t = {
    id : ID.t;
    formal_in_params : 'v Params.M.t;
    formal_out_params : 'v Params.M.t;
    graph : G.t;
    locals : 'v Var.Decls.t;
    local_ids : ID.generator;
    block_ids : ID.generator;
    specification : ('v, 'e) proc_spec option;
  }

  let add_goto p ~(from : ID.t) ~(targets : ID.t list) =
    let open Vert in
    let g = p.graph in
    let fr = End from in
    List.iter (fun t -> G.add_edge g fr (Begin t)) targets

  let create id ?(formal_in_params = Params.M.empty)
      ?(formal_out_params = Params.M.empty) ?(captures_globs = [])
      ?(modifies_globs = []) ?(requires = []) ?(ensures = []) () =
    let graph = G.create () in
    let specification =
      Some { captures_globs; modifies_globs; requires; ensures }
    in
    G.add_vertex graph Entry;
    G.add_vertex graph Exit;
    G.add_vertex graph Return;
    {
      id;
      formal_in_params;
      formal_out_params;
      graph;
      locals = Var.Decls.empty ();
      local_ids = ID.make_gen ();
      block_ids = ID.make_gen ();
      specification;
    }

  let add_block p id ?(phis = []) ~(stmts : ('var, 'var, 'expr) Stmt.t list)
      ?(successors = []) () =
    let stmts = Vector.of_list stmts in
    let b = Edge.(Block { phis; stmts }) in
    let open Vert in
    let existing = G.find_all_edges p.graph (Begin id) (End id) in
    List.iter (fun e -> G.remove_edge_e p.graph e) existing;
    G.add_edge_e p.graph (Begin id, b, End id);
    List.iter (fun i -> G.add_edge p.graph (End id) (Begin i)) successors

  let decl_block_exn p name ?(phis = [])
      ~(stmts : ('var, 'var, 'expr) Stmt.t list) ?(successors = []) () =
    let open Block in
    let id = p.block_ids.decl_exn name in
    add_block p id ~phis ~stmts ~successors ();
    id

  let fresh_block p ?name ?(phis = [])
      ~(stmts : ('var, 'var, 'expr) Stmt.t list) ?(successors = []) () =
    let open Block in
    let name = Option.get_or ~default:"block" name in
    let id = p.block_ids.fresh ~name () in
    add_block p id ~phis ~stmts ~successors ();
    id

  let add_return p ~(from : ID.t) ~(args : BasilExpr.t Params.M.t) =
    let open Vert in
    let fr = End from in
    let b =
      Edge.(
        Block
          { phis = []; stmts = Vector.of_list [ Stmt.(Instr_Return { args }) ] })
    in
    G.add_edge_e p.graph (fr, b, Return)

  let get_entry_block p id =
    let open Edge in
    let open G in
    try
      let id = G.find_edge p.graph Entry (Begin id) in
      Some id
    with Not_found -> None

  let get_block p id =
    let open Edge in
    let open G in
    try
      let _, e, _ = G.find_edge p.graph (Begin id) (End id) in
      match e with Block b -> Some b | Jump -> None
    with Not_found -> None

  let update_block p id (block : (Var.t, BasilExpr.t) Block.t) =
    let open Edge in
    let open G in
    G.remove_edge p.graph (Begin id) (End id);
    G.add_edge_e p.graph (Begin id, Block block, End id)

  let replace_edge p id (block : (Var.t, BasilExpr.t) Block.t) =
    update_block p id block

  let decl_local p v =
    let _ = p.local_ids.decl_or_get (Var.name v) in
    Var.Decls.add p.locals v;
    v

  let fresh_var p ?(pure = true) typ =
    let n, _ = p.local_ids.fresh ~name:"v" () in
    let v = Var.create n typ ~pure in
    Var.Decls.add p.locals v;
    v

  let blocks_to_list p =
    let collect_edge edge acc =
      let id = G.V.label (G.E.src edge) in
      let edge = G.E.label edge in
      match edge with Edge.(Block b) -> (id, b) :: acc | _ -> acc
    in
    G.fold_edges_e collect_edge p.graph []

  let pretty show_lvar show_var show_expr p =
    let open Containers_pp in
    let open Containers_pp.Infix in
    let params m =
      Params.M.to_list m
      |> List.map (function i, p -> show_var p)
      |> List.map text
      |> fun s -> bracket "(" (fill (text "," ^ newline_or_spaces 1) s) ")"
    in
    let header =
      text "proc "
      ^ text (ID.to_string p.id)
      ^ nest 2
          (fill
             (newline ^ text " -> ")
             [ params p.formal_in_params; params p.formal_out_params ])
    in
    let collect_edge b ende acc =
      let vert = G.V.label b in
      let edge = G.E.label (G.find_edge p.graph b ende) in
      match (vert, edge) with
      | Vert.Begin block_id, Edge.(Block b) ->
          let succ = G.succ p.graph ende in
          let succ =
            match succ with
            | [ Return ] -> (
                let _, re, _ = G.find_edge p.graph ende Return in
                match re with
                | Block { stmts } ->
                    Vector.map
                      (fun s ->
                        Stmt.pretty show_lvar show_var show_expr s ^ text ";")
                      stmts
                    |> Vector.to_list
                | _ -> failwith "bad return")
            | [] -> [ text "unreachable;" ]
            | succ ->
                let succ =
                  List.map
                    (fun f ->
                      match G.V.label f with
                      | Begin i -> text @@ ID.to_string i
                      | _ -> failwith "unsupp")
                    succ
                in
                [
                  text "goto "
                  ^ (fun s -> bracket "(" (fill (text ",") s) ")") succ
                  ^ text ";";
                ]
          in
          let b =
            Block.pretty show_lvar show_var show_expr ~block_id ~terminator:succ
              b
          in
          b :: acc
      | _ -> acc
    in
    let blocks = G.fold_edges collect_edge p.graph [] in
    let blocks =
      surround (text "[")
        (nest 2 @@ newline
        ^ append_l ~sep:(text ";" ^ newline) (List.rev blocks))
        (newline ^ text "]")
    in
    header ^ nl ^ blocks
end

module Program = struct
  type e = BasilExpr.t
  type proc = (Var.t, BasilExpr.t) Procedure.t
  type bloc = (Var.t, BasilExpr.t) Block.t
  type stmt = (Var.t, Var.t, e) Stmt.t

  type t = {
    modulename : string;
    globals : Var.t Var.Decls.t;
    entry_proc : ID.t option;
    procs : proc ID.Map.t;
    proc_names : ID.generator;
  }

  let proc_pretty chan p =
    let p =
      Procedure.pretty Var.to_string_il_lvar Var.to_string_il_rvar
        Expr.BasilExpr.to_string p
    in
    output_string chan @@ Containers_pp.Pretty.to_string ~width:80 p;
    output_string chan ";"

  let prog_pretty (p : t) =
    let open Containers_pp in
    let open Containers_pp.Infix in
    let globs =
      Var.Decls.to_list p.globals
      |> List.map (fun (n, v) -> text @@ Var.to_decl_string_il v)
    in
    let n =
      p.entry_proc
      |> Option.map (fun i -> text "prog entry " ^ text @@ ID.to_string i)
      |> Option.to_list
    in
    let pretty =
      append_l ~sep:(text ";\n")
      @@ globs @ n
      @ List.map
          (fun (_, p) ->
            Procedure.pretty Var.to_string_il_lvar Var.to_string_il_rvar
              Expr.BasilExpr.to_string p)
          (ID.Map.to_list p.procs)
    in
    pretty

  let pretty_to_chan chan (p : t) =
    let p = prog_pretty p in
    output_string chan @@ Containers_pp.Pretty.to_string ~width:80 p;
    output_string chan ";"

  let decl_global p = Var.Decls.add p.globals

  let empty ?name () =
    let modulename = Option.get_or ~default:"<module>" name in
    {
      modulename;
      entry_proc = None;
      globals = Var.Decls.empty ();
      procs = ID.Map.empty;
      proc_names = ID.make_gen ();
    }

  module CallGraph = struct
    module Vert = struct
      type t =
        | ProcBegin of ID.t
        | ProcReturn of ID.t
        | ProcExit of ID.t
        | Entry
        | Return (*| Exit*)
      [@@deriving show { with_path = false }, eq, ord]

      let hash (v : t) =
        let h = Hash.pair Hash.int Hash.int in
        Hash.map
          (function
            | ProcBegin i -> (31, ID.hash i)
            | ProcReturn i -> (37, ID.hash i)
            | ProcExit i -> (41, ID.hash i)
            | o -> (Hashtbl.hash o, 1))
          h v
    end

    module Edge = struct
      type t = Proc of ID.t | Nop
      [@@deriving show { with_path = false }, eq, ord]

      let default = Nop
    end

    module G =
      Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Vert) (Edge)

    let make_call_graph t =
      let called_by (p : proc) =
        Procedure.blocks_to_list p |> List.to_iter |> Iter.map snd
        |> Iter.flat_map Block.stmts_iter
        |> Iter.filter_map (function
          | Stmt.Instr_Call { procid } -> Some procid
          | _ -> None)
        |> ID.Set.of_iter
      in
      let calls =
        ID.Map.to_iter t.procs
        |> Iter.map (function pid, proc -> (pid, called_by proc))
      in
      let graph = G.create ~size:(ID.Map.cardinal t.procs) () in
      let open Edge in
      let open Vert in
      let proc_edges =
        Iter.map
          (function id -> (ProcBegin id, Proc id, ProcReturn id))
          (ID.Map.keys t.procs)
      in
      Iter.iter (G.add_edge_e graph) proc_edges;
      t.entry_proc
      |> Option.iter (fun entry ->
          List.iter (G.add_edge_e graph)
            [ (Entry, Nop, ProcBegin entry); (ProcReturn entry, Nop, Return) ]);
      let call_dep caller callee =
        Iter.of_list
          [
            (ProcBegin caller, Nop, ProcBegin callee);
            (ProcReturn callee, Nop, ProcReturn caller);
          ]
      in
      let call_dep_edges =
        Iter.flat_map
          (function
            | proc, called ->
                Iter.append
                  (Iter.singleton (ProcBegin proc, Proc proc, ProcReturn proc))
                  (Iter.flat_map
                     (function c -> call_dep proc c)
                     (ID.Set.to_iter called)))
          calls
      in
      Iter.iter (G.add_edge_e graph) call_dep_edges;
      graph
  end
end
