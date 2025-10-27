open Value
open Common
open Types
open Expr
open ContainersLabels

module ID = struct
  include Int
  module Map = Map.Make (Int)

  module Named = struct
    (* generator for unique integer identifiers with an optionally associated name.
       maintains a mapping between id and name.

       note: ID.t is the canonical identifier,
        with the associated name assumed to be unique with respect to it.
       *)
    module M = CCBijection.Make (String) (Int)

    type cache = { names : M.t ref; gen : Fix.Gensym.gensym }

    let get_id c name = M.find_left name !(c.names)
    let get_name c id = M.find_right id !(c.names)

    let fresh c ?(name : string option) () =
      let id = c.gen () in
      Option.iter (fun n -> c.names := M.add n id !(c.names)) name;
      id

    type t = {
      get_id : string -> int;
      get_name : int -> string;
      fresh : ?name:string -> unit -> int;
    }

    let make () =
      let c = { names = ref M.empty; gen = Fix.Gensym.make () } in
      { get_id = get_id c; fresh = fresh c; get_name = get_name c }
  end
end

module Params = struct
  module M = Map.Make (String) [@@deriving show]

  type formal = Var.t M.t [@@deriving eq, ord]
  type actual = BasilExpr.t M.t [@@deriving eq, ord]
  type lhs = Var.t M.t [@@deriving eq, ord]

  let show_actual a =
    M.to_list a
    |> List.map ~f:(function k, v ->
           Printf.sprintf "%s -> %s" k (BasilExpr.to_string v))
    |> String.concat ~sep:", "
    |> fun x -> "(" ^ x ^ ")"

  let pp_actual fmt a = Format.pp_print_string fmt (show_actual a)

  let show_formal (a : formal) =
    M.to_list a
    |> List.map ~f:(function k, v ->
           Printf.sprintf "%s -> %s" k (Var.to_string v))
    |> String.concat ~sep:", "
    |> fun x -> "(" ^ x ^ ")"

  let pp_formal fmt a = Format.pp_print_string fmt (show_formal a)

  let show_lhs (a : lhs) =
    M.to_list a
    |> List.map ~f:(function k, v ->
           Printf.sprintf "%s <- %s" (Var.to_string v) k)
    |> String.concat ~sep:", "
    |> fun x -> "(" ^ x ^ ")"

  let pp_lhs fmt a = Format.pp_print_string fmt (show_lhs a)
end

module Call = struct
  type ('lvar, 'expr) t =
    | Instr_Return of { args : 'expr Params.M.t }
    | Instr_Call of {
        lhs : 'lvar Params.M.t;
        procid : ID.t;
        args : 'expr Params.M.t;
      }
    | Instr_IndirectCall of { target : 'expr }
  [@@deriving eq, ord, map]

  let fold ~f_lvar ~f_rvar ~f_expr init e =
    match e with
    | Instr_IndirectCall { target } -> f_expr init target
    | Instr_Call { lhs; procid; args } ->
        let args = Params.M.to_list args |> List.map ~f:snd in
        let lhs = Params.M.to_list lhs |> List.map ~f:snd in
        List.fold_left ~f:f_expr ~init args |> fun i ->
        List.fold_left ~f:f_lvar ~init:i lhs
    | Instr_Return { args } ->
        let args = Params.M.to_list args |> List.map ~f:snd in
        List.fold_left ~f:f_expr ~init args

  let to_string c =
    let param_list l =
      if Params.M.is_empty l then ""
      else
        "("
        ^ (Params.M.to_list l
          |> List.map ~f:(function k, v -> k ^ " -> " ^ v)
          |> String.concat ~sep:", ")
        ^ ")"
    in
    let c = map Var.to_string BasilExpr.to_string c in
    match c with
    | Instr_Call { lhs; procid; args } ->
        let n = Int.to_string procid in
        param_list lhs ^ " := call " ^ n ^ param_list args
    | Instr_Return { args } -> "return " ^ param_list args
    | Instr_IndirectCall { target } -> "indirect_call " ^ target
end

module Stmt = struct
  type endian = [ `Big | `Little ] [@@deriving eq, ord]
  type ident = string

  let show_endian = function `Big -> "be" | `Little -> "le"
  let pp_endian fmt e = Format.pp_print_string fmt (show_endian e)

  type ('lvar, 'var, 'expr) t =
    | Instr_Assign of ('lvar * 'expr) list  (** simultaneous assignment *)
    | Instr_Assert of { body : 'expr }  (** assertions *)
    | Instr_Assume of { body : 'expr; branch : bool }  (** load from memory *)
    | Instr_Load of { lhs : 'lvar; mem : 'var; addr : 'expr; endian : endian }
        (** effectful operation calling a named intrinsic*)
    | Instr_IntrinCall of {
        lhs : 'lvar Params.M.t;
        name : string;
        args : 'expr Params.M.t;
      }  (** a store to memory *)
    | Instr_Store of {
        mem : 'var;
        addr : 'expr;
        value : 'expr;
        endian : endian;
      }
  [@@deriving eq, ord, map]

  let map ~f_lvar ~f_expr e =
    let f_rvar v = f_expr (BasilExpr.rvar v) in
    map f_lvar f_rvar f_expr e

  (** TODO: this isn't really a sensible operation I think; would probably make
      more sense to just have a 'subexprs' and 'lvars' functions (which return
      iters)*)
  let fold ~(f_lvar : 'a -> 'lv -> 'a) ~(f_rvar : 'a -> 'v -> 'a)
      ~(f_expr : 'a -> 'e -> 'a) ~(init : 'a) (e : ('lv, 'v, 'e) t) : 'a =
    match e with
    | Instr_Assign ls ->
        List.fold_left ~f:f_expr ~init (List.map ~f:snd ls) |> fun i ->
        List.fold_left ~f:f_lvar ~init:i (List.map ~f:fst ls)
    | Instr_Assert { body } -> f_expr init body
    | Instr_Assume { body } -> f_expr init body
    | Instr_Load { lhs; mem; addr; endian } ->
        f_expr init addr |> fun i ->
        f_rvar i mem |> fun i -> f_lvar i lhs
    | Instr_Store { mem; addr; value; endian } ->
        f_expr init value |> fun i ->
        f_expr i addr |> fun i -> f_rvar i mem
    | Instr_IntrinCall { lhs; name; args } ->
        let args = Params.M.to_list args |> List.map ~f:snd in
        let lhs = Params.M.to_list lhs |> List.map ~f:snd in
        List.fold_left ~f:f_expr ~init args |> fun i ->
        List.fold_left ~f:f_lvar ~init:i lhs

  let to_string show_var show_expr (s : (Var.t, Var.t, BasilExpr.t) t) =
    let param_list l =
      if Params.M.is_empty l then ""
      else
        "("
        ^ (Params.M.to_list l
          |> List.map ~f:(function k, v -> k ^ " -> " ^ v)
          |> String.concat ~sep:", ")
        ^ ")"
    in
    map ~f_lvar:show_var ~f_expr:show_expr s |> function
    | Instr_Assign ls ->
        List.map ~f:(function lhs, rhs -> lhs ^ " := " ^ rhs) ls
        |> String.concat ~sep:", "
    | Instr_Assert { body } -> "assert " ^ body
    | Instr_Assume { body; branch = false } -> "assume " ^ body
    | Instr_Assume { body; branch = true } -> "guard " ^ body
    | Instr_Load { lhs; mem; addr; endian } ->
        lhs ^ " := " ^ "load_" ^ show_endian endian ^ " " ^ addr
    | Instr_Store { mem; addr; value; endian } ->
        "store_" ^ show_endian endian ^ " " ^ addr ^ " " ^ value
    | Instr_IntrinCall { lhs; name; args } ->
        param_list lhs ^ " := call " ^ name ^ param_list args
end

module Block = struct
  type 'var phi = Phi of { lhs : 'var; rhs : (ID.t * 'var) list }
  [@@deriving eq, ord, show]

  type ('v, 'e) t = {
    id : ID.t;
    phis : 'v phi list;
    stmts : ('v, 'v, 'e) Stmt.t list;
    call : ('v, 'e) Call.t option;
  }
  [@@deriving eq, ord]

  let to_string b =
    let c =
      Option.map (fun c -> Printf.sprintf ";\n  %s" (Call.to_string c)) b.call
      |> Option.get_or ~default:""
    in
    let stmts =
      List.map
        ~f:(fun stmt -> Stmt.to_string Var.to_string BasilExpr.to_string stmt)
        b.stmts
      |> String.concat ~sep:";\n  "
    in
    Printf.sprintf "block %d [\n  %s%s]\n" b.id stmts c

  let fold_stmt_forwards ~(phi : 'acc -> 'v phi list -> 'acc)
      ~(f : 'acc -> ('v, 'v, 'e) Stmt.t -> 'acc) (i : 'a) (b : ('v, 'e) t) :
      'acc =
    List.fold_left ~f ~init:(phi i b.phis) b.stmts

  let fold_stmt_backwards ~(f : 'acc -> ('v, 'v, 'e) Stmt.t -> 'acc)
      ~(phi : 'acc -> 'v phi list -> 'acc) ~(init : 'a) (b : ('v, 'e) t) : 'acc
      =
    List.fold_right ~f:(fun stmt acc -> f acc stmt) ~init b.stmts |> fun e ->
    phi e b.phis
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
          | Begin i -> (31, i)
          | End i -> (37, i))
        h v
  end

  module Edge = struct
    type block = (Var.t, BasilExpr.t) Block.t [@@deriving eq, ord]
    type t = Block of block | Jump [@@deriving eq, ord]

    let show = function Block b -> Block.to_string b | Jump -> "goto"
    let to_string = function Block b -> Block.to_string b | Jump -> "goto"
    let default = Jump
  end

  module Loc = Int
  module G = Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Vert) (Edge)

  type t = {
    id : ID.t;
    formal_in_params : Params.formal;
    formal_out_params : Params.formal;
    captures_globs : Var.Decls.t;
    modifies_globs : Var.Decls.t;
    requires : BasilExpr.t list;
    ensures : BasilExpr.t list;
    locals : Var.Decls.t;
    graph : G.t;
    gensym : Fix.Gensym.gensym;
    gensym_bloc : Fix.Gensym.gensym;
  }

  let add_goto p ~(from : ID.t) ~(targets : ID.t list) =
    let open Vert in
    let g = p.graph in
    let fr = End from in
    List.iter ~f:(fun t -> G.add_edge g fr (Begin t)) targets

  let create id ?(formal_in_params = Params.M.empty)
      ?(formal_out_params = Params.M.empty)
      ?(captures_globs = Var.Decls.empty ())
      ?(modifies_globs = Var.Decls.empty ()) ?(requires = []) ?(ensures = [])
      ?(locals = Var.Decls.empty ()) ?(blocks = Vector.create ()) () =
    let graph = G.create () in
    G.add_vertex graph Entry;
    G.add_vertex graph Exit;
    G.add_vertex graph Return;
    {
      id;
      formal_in_params;
      formal_out_params;
      captures_globs;
      modifies_globs;
      requires;
      ensures;
      graph;
      locals;
      gensym = Fix.Gensym.make ();
      gensym_bloc = Fix.Gensym.make ();
    }

  (*
  let update_block_by_index p (b : ('a, 'b) Block.t) =
    let i =
      Hashtbl.get p.block_i b.id |> Option.get_exn_or "update nonexistent block"
    in
    Vector.set p.blocks i b
    *)

  let fresh_block p ?(phis = []) ~(stmts : ('var, 'var, 'expr) Stmt.t list)
      ?(successors = []) ?call () =
    let open Block in
    let id = p.gensym_bloc () in
    let b = Edge.(Block { id; phis; stmts; call }) in
    let open Vert in
    G.add_vertex p.graph (Begin id);
    G.add_vertex p.graph (Begin id);
    G.add_edge_e p.graph (Begin id, b, End id);
    List.iter ~f:(fun i -> G.add_edge p.graph (End id) (Begin i)) successors;
    id

  let add_return p ~(from : ID.t) ~(args : BasilExpr.t Params.M.t) =
    let open Vert in
    let fr = End from in
    let id = p.gensym_bloc () in
    let b =
      Edge.(
        Block
          {
            id;
            phis = [];
            stmts = [];
            call = Some (Call.Instr_Return { args });
          })
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

  let update_block p (block : (Var.t, BasilExpr.t) Block.t) =
    let open Edge in
    let open G in
    let id = block.id in
    G.remove_edge p.graph (Begin id) (End id);
    G.add_edge_e p.graph (Begin id, Block block, End id)

  let fresh_var p ?(pure = true) typ =
    let n = "v" ^ Int.to_string (p.gensym ()) in
    let v = Var.create n typ ~pure in
    Var.Decls.add p.locals v;
    v

  let copy e = { e with graph = G.copy e.graph }
end

module Program = struct
  type e = BasilExpr.t
  type proc = Procedure.t
  type bloc = (Var.t, BasilExpr.t) Block.t
  type stmt = (Var.t, Var.t, e) Stmt.t
  type call = (Var.t, e) Call.t

  type t = {
    modulename : string;
    globals : Var.Decls.t;
    procs : proc ID.Map.t;
    proc_names : ID.Named.t;
  }

  let decl_glob p = Var.Decls.add p.globals

  let empty ?name () =
    let modulename = Option.get_or ~default:"<module>" name in
    {
      modulename;
      globals = Var.Decls.empty ();
      procs = ID.Map.empty;
      proc_names = ID.Named.make ();
    }
end
