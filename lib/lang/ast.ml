open Common
open Containers
open Value

module Var = struct
  module V = struct
    type t = { name : string; typ : Types.BType.t; pure : bool }
    [@@deriving eq, ord]

    let var name ?(pure = true) typ = { name; typ; pure }
    let hash v = Hashtbl.hash v
  end

  module H = Fix.HashCons.ForHashedTypeWeak (V)

  type t = V.t Fix.HashCons.cell

  let create name ?(pure = false) typ = H.make { name; typ; pure }
  let name (e : t) = (Fix.HashCons.data e).name
  let typ (e : t) = (Fix.HashCons.data e).typ
  let pure (e : t) = (Fix.HashCons.data e).pure
  let compare (a : t) (b : t) = Fix.HashCons.compare a b
  let equal (a : t) (b : t) = Fix.HashCons.equal a b
  let hash (a : t) = Fix.HashCons.hash a

  module Set = CCHashSet.Make (V)
  module Bindings = CCHashTrie.Make (V)

  module Decls = struct
    type var = t
    type t = (string, var) Hashtbl.t

    let find_opt m name = Hashtbl.find_opt m name
    let empty () : t = Hashtbl.create 30

    let add m (v : var) =
      let d = find_opt m (name v) in
      match d with
      | Some e when equal e v -> ()
      | Some e -> failwith "Already declared diff var with that name: "
      | None -> Hashtbl.add m (name v) v
  end
end

module AbstractExpr = struct
  type ('const, 'var, 'unary, 'binary, 'intrin, 'e) t =
    | RVar of 'var  (** variables *)
    | Constant of 'const
        (** constants; a pure intrinsic function with zero arguments *)
    | UnaryExpr of 'unary * 'e
        (** application of a pure intrinsic function with one arguments *)
    | BinaryExpr of 'binary * 'e * 'e
        (** application of a pure intrinsic function with two arguments *)
    | ApplyIntrin of 'intrin * 'e list
        (** application of a pure intrinsic function with n arguments *)
    | ApplyFun of string * 'e list
        (** application of a pure runtime-defined function with n arguments *)
    | Binding of 'var list * 'e  (** syntactic binding in a nested scope *)
  [@@deriving eq, ord, fold, map, iter]

  let id a b = a
  let ofold = fold
  let fold f b o = ofold id id id id id f b o
  let omap = map

  let map f e =
    let id a = a in
    omap id id id id id f e

  let hash hash e1 =
    let hash_const = Hashtbl.hash in
    let hash_var = Hashtbl.hash in
    let hash_unary = Hashtbl.hash in
    let hash_binary = Hashtbl.hash in
    let hash_intrin = Hashtbl.hash in
    let open HashHelper in
    match e1 with
    | RVar r -> combine 1 (hash_var r)
    | UnaryExpr (op, a) -> combine2 3 (hash_unary op) (hash a)
    | BinaryExpr (op, l, r) -> combine3 5 (hash_binary op) (hash l) (hash r)
    | Constant c -> combine 7 (hash_const c)
    | ApplyIntrin (i, args) ->
        combine 11 (combinel (hash_intrin i) (List.map hash args))
    | ApplyFun (n, args) ->
        combine 13 (combinel (String.hash n) (List.map hash args))
    | Binding (args, body) ->
        combine 17 (combinel (hash body) (List.map hash_var args))

  (*
  type ('const, 'var, 'unary, 'binary, 'intrin, 'e) abs =
    ('const, 'var, 'unary, 'binary, 'intrin, 'e) t

  module Final (F : sig
    type 'v t
    type const
    type unary
    type binary
    type intrin

    val fix : (const, 'v, unary, binary, intrin, 'v t) abs -> 'v t
    val unfix : 'v t -> (const, 'v, unary, binary, intrin, 'v t) abs
  end) =
  struct
    let ( >> ) = fun f g x -> g (f x)
    let rec cata alg e = (F.unfix >> map (cata alg) >> alg) e
  end
  *)
end

module Maps = struct
  (* map, value -> result *)
  type binary = [ `MapIndex ] [@@deriving show { with_path = false }, eq, ord]
  type intrin = [ `MapUpdate ] [@@deriving show { with_path = false }, eq, ord]

  let show = function
    | #binary as b -> show_binary b
    | #intrin as b -> show_intrin b

  let hash = Hashtbl.hash
end

module LogicalOps = struct
  type const = [ `Bool of bool ]
  [@@deriving show { with_path = false }, eq, ord]

  type unary = [ `LNOT ] [@@deriving show { with_path = false }, eq, ord]

  type binary = [ `EQ | `NEQ | `IMPLIES ]
  [@@deriving show { with_path = false }, eq, ord]

  type intrin = [ `AND | `OR ] [@@deriving show { with_path = false }, eq, ord]

  let show = function
    | #const as c -> show_const c
    | #unary as u -> show_unary u
    | #binary as b -> show_binary b

  let hash_boolop = Hashtbl.hash
end

module BVOps = struct
  type const = [ `Bitvector of PrimQFBV.t ]
  [@@deriving show { with_path = false }, eq, ord]

  type unary = [ `BVNOT | `BVNEG | `BOOL2BV1 ]
  [@@deriving show { with_path = false }, eq, ord]

  type binary =
    [ `BVAND
    | `BVOR
    | `BVADD
    | `BVMUL
    | `BVUDIV
    | `BVUREM
    | `BVSHL
    | `BVLSHR
    | `BVNAND
    | `BVNOR
    | `BVXOR
    | `BVXNOR
    | `BVCOMP
    | `BVSUB
    | `BVSDIV
    | `BVSREM
    | `BVSMOD
    | `BVASHR
    | `BVULT
    | `BVULE
    | `BVSLT
    | `BVSLE
    | `BVConcat ]
  [@@deriving show { with_path = false }, eq, ord]

  type intrin =
    [ `ZeroExtend of int
    | `SignExtend of int
    | `Extract of int * int
    | `BVAND
    | `BVOR
    | `BVADD
    | `BVXOR ]
  [@@deriving show { with_path = false }, eq, ord]

  let show = function
    | #const as c -> show_const c
    | #unary as u -> show_unary u
    | #binary as b -> show_binary b
end

module IntOps = struct
  type const = [ `Integer of PrimInt.t ]
  [@@deriving show { with_path = false }, eq, ord]

  type unary = [ `INTNEG ] [@@deriving show { with_path = false }, eq, ord]

  type binary =
    [ `INTADD | `INTMUL | `INTSUB | `INTDIV | `INTMOD | `INTLT | `INTLE ]
  [@@deriving show { with_path = false }, eq, ord]

  let show = function
    | #const as c -> show_const c
    | #unary as u -> show_unary u
    | #binary as b -> show_binary b
end

module Spec = struct
  type unary = [ `Forall | `Old | `Exists ]
  [@@deriving show { with_path = false }, eq, ord]

  let hash_intrin a = Hashtbl.hash a
end

module type Ops = sig
  type const
  type unary
  type binary
  type intrin

  val hash_const : const -> int
  val hash_unary : unary -> int
  val hash_binary : binary -> int
  val hash_intrin : intrin -> int
  val pp_const : Format.formatter -> const -> unit
  val show_const : const -> string
  val equal_const : const -> const -> bool
  val pp_unary : Format.formatter -> unary -> unit
  val show_unary : unary -> string
  val equal_unary : unary -> unary -> bool
  val pp_binary : Format.formatter -> binary -> unit
  val show_binary : binary -> string
  val equal_binary : binary -> binary -> bool
  val pp_intrin : Format.formatter -> intrin -> unit
  val show_intrin : intrin -> string
  val equal_intrin : intrin -> intrin -> bool

  type ('var, 'e) t = (const, 'var, unary, binary, intrin, 'e) AbstractExpr.t
end

module AllOps = struct
  type const = [ IntOps.const | BVOps.const | LogicalOps.const ]
  [@@deriving show { with_path = false }, eq, ord]

  type unary = [ IntOps.unary | BVOps.unary | Spec.unary | LogicalOps.unary ]
  [@@deriving show { with_path = false }, eq, ord]

  type binary =
    [ IntOps.binary | BVOps.binary | Maps.binary | LogicalOps.binary ]
  [@@deriving show { with_path = false }, eq, ord]

  type intrin = [ BVOps.intrin | Maps.intrin | LogicalOps.intrin ]
  [@@deriving show { with_path = false }, eq, ord]

  let hash_const = Hashtbl.hash
  let hash_unary = Hashtbl.hash
  let hash_binary = Hashtbl.hash
  let hash_intrin = Hashtbl.hash

  type ('var, 'e) t = (const, 'var, unary, binary, intrin, 'e) AbstractExpr.t
end

module Recursion (E : sig
  type 'e node

  val fix : 'e node -> 'e
  val unfix : 'a -> 'a node
  val map : ('a -> 'b) -> 'a node -> 'b node
end) =
struct
  let ( >> ) = fun f g x -> g (f x)

  let rec cata : 'b. ('b E.node -> 'b) -> 'e -> 'b =
   fun alg -> E.unfix >> E.map (cata alg) >> alg
end

module Final = struct
  include AbstractExpr

  type ('a, 'b, 'c, 'd, 'e, 'f) abs_expr = ('a, 'b, 'c, 'd, 'e, 'f) t
  [@@deriving eq, ord]

  type ('a, 'b, 'c, 'd, 'e) t = ('a, 'b, 'c, 'd, 'e) expr_node_v

  and ('a, 'b, 'c, 'd, 'e) expr_node_v =
    | E of ('a, 'b, 'c, 'd, 'e, ('a, 'b, 'c, 'd, 'e) t) abs_expr
  [@@deriving eq, ord]

  let fix (e : ('a, 'b, 'c, 'd, 'e, ('a, 'b, 'c, 'd, 'e) t) abs_expr) = E e

  let unfix (e : ('a, 'b, 'c, 'd, 'e) t) :
      ('a, 'b, 'c, 'd, 'e, ('a, 'b, 'c, 'd, 'e) t) abs_expr =
    match e with E e -> e
end

module Alges = struct
  open AbstractExpr

  let children_alg a =
    let alg a = fold (fun acc a -> a @ acc) [] a in
    alg

  let hash_alg (hash_const : 'a -> int) (hash_var : 'b -> int) =
    let alg a =
      match a with
      | RVar v -> hash_var v
      | Constant c -> hash_const c
      | UnaryExpr (op, e) -> Hash.pair Hashtbl.hash Fun.id (Hashtbl.hash op, e)
      | BinaryExpr (op, e, e2) ->
          Hash.triple Hashtbl.hash Fun.id Fun.id (Hashtbl.hash op, e, e2)
      | ApplyIntrin (op, es) ->
          Hash.pair Hashtbl.hash (Hash.list Fun.id) (op, es)
      | ApplyFun (n, es) -> Hash.pair Hash.string (Hash.list Fun.id) (n, es)
      | Binding (vs, b) -> Hash.pair (Hash.list hash_var) Fun.id (vs, b)
    in
    alg
end

module type Fix = sig
  type const
  type var
  type unary
  type binary
  type intrin
  type t

  val fix : (const, var, unary, binary, intrin, t) AbstractExpr.t -> t
  val unfix : t -> (const, var, unary, binary, intrin, t) AbstractExpr.t
end

module SmartConstr (O : Fix) = struct
  open O

  let ( >> ) = fun f g x -> g (f x)
  let rec cata alg e = (unfix >> AbstractExpr.map (cata alg) >> alg) e
  let rvar v = fix (RVar v)
  let const v = fix (Constant v)
  let intconst v = fix (Constant v)
  let binexp ~op l r = fix (BinaryExpr (op, l, r))
  let unexp ~op arg = fix (UnaryExpr (op, arg))
  let fapply id params = fix (ApplyFun (id, params))
  let binding params body = fix (Binding (params, body))
  let identity x = x
  let applyintrin ~op params = fix (ApplyIntrin (op, params))
  let apply_fun ~name params = fix (ApplyFun (name, params))
end

(*
module FixExpr (O : Ops) = struct
  module F = struct
    type const = O.const
    type unary = O.unary
    type binary = O.binary
    type intrin = O.intrin

    type 'v t = 'v expr_node_v

    and 'v expr_node_v =
      | E of (const, 'v, unary, binary, intrin, 'v t) AbstractExpr.t

    let fix e = E e
    let unfix e = match e with E e -> e
  end

  include F
  include AbstractExpr.Final (F)

  (* smart constructors*)
  let const v = fix (Constant v)
  let binexp ~op l r = fix (BinaryExpr (op, l, r))
  let unexp ~op arg = fix (UnaryExpr (op, arg))
  let fapply id params = fix (ApplyFun (id, params))
  let applyintrin id params = fix (ApplyIntrin (id, params))
  let identity x = x
end
*)

module BasilExpr = struct
  include Final

  module E = struct
    include AllOps

    type var = Var.t
    type 'a cell = 'a Fix.HashCons.cell

    let equal_cell _ a b = Fix.HashCons.equal a b
    let compare_cell _ a b = Fix.HashCons.compare a b

    type t = expr_node_v cell

    and expr_node_v =
      | E of (const, Var.t, unary, binary, intrin, t) AbstractExpr.t
    [@@deriving eq, ord]

    module HashExpr = struct
      type t = expr_node_v

      let hash e : int =
        e |> function E e -> AbstractExpr.hash Fix.HashCons.hash e

      let equal (i : t) (j : t) : bool =
        match (i, j) with
        | E i, E j ->
            AbstractExpr.equal AllOps.equal_const Var.equal AllOps.equal_unary
              AllOps.equal_binary AllOps.equal_intrin Fix.HashCons.equal i j
    end

    module H = Fix.HashCons.ForHashedTypeWeak (HashExpr)

    let fix i = H.make (E i)
    let unfix i = match Fix.HashCons.data i with E i -> i
  end

  include E
  module R = SmartConstr (E)
  include R

  let hash_abs = hash
  let intconst (v : PrimInt.t) : t = const (`Integer v)
  let boolconst (v : bool) : t = const (`Bool v)
  let bvconst (v : PrimQFBV.t) : t = const (`Bitvector v)
  let load_expr (mem : Var.t) index : t = binexp ~op:`MapIndex (rvar mem) index

  let zero_extend ~n_prefix_bits (e : t) : t =
    applyintrin ~op:(`ZeroExtend n_prefix_bits) [ e ]

  let sign_extend ~n_prefix_bits (e : t) : t =
    applyintrin ~op:(`SignExtend n_prefix_bits) [ e ]

  let extract ~hi_incl ~lo_excl (e : t) : t =
    applyintrin ~op:(`Extract (hi_incl, lo_excl)) [ e ]

  let concat (e : t) (f : t) : t = binexp ~op:`BVConcat e f
  let forall ~bound p = unexp ~op:`Forall (binding bound p)
  let exists ~bound p = unexp ~op:`Exists (binding bound p)
  let boolnot e = unexp ~op:`LNOT e
end
