open Common
open Containers

(* workaround: ZArith library doesn't like zero-length extracts *)
let checked_extract f v off len = if len > 0 then f v off len else Z.zero
let z_extract = checked_extract Z.extract
let z_signed_extract = checked_extract Z.signed_extract

module PrimInt = struct
  type t = Z.t

  let pp = Z.pp_print
  let show i = Z.to_string i
  let equal i j = Z.equal i j
  let compare i j = Z.compare i j
  let hash i = Z.hash i
end

module PrimQFBV = struct
  (* representation of bitvector positive Z.t and an explicit width*)

  type t = { w : int; v : Z.t }

  let show (b : t) = Printf.sprintf "0x%s:bv%d" (Z.format "%x" @@ b.v) b.w
  let pp fmt b = Format.pp_print_string fmt (show b)
  let hash b = HashHelper.combine (Int.hash b.w) (Z.hash b.v)
  let ones ~(size : int) = z_extract Z.minus_one 0 size
  let zero ~(size : int) = { w = size; v = Z.zero }
  let empty = zero ~size:0
  let is_zero b = Z.equal Z.zero b.v
  let width (x : t) = match x with { w; v } -> w
  let value (b : t) : Z.t = match b with { w; v } -> v
  let to_signed_bigint b = z_signed_extract b.v 0 b.w
  let to_unsigned_bigint b = z_extract b.v 0 b.w
  let is_negative b = Z.lt (to_signed_bigint b) Z.zero
  let equal a b = Int.equal a.w b.w && Z.equal a.v b.v

  let compare a b =
    Int.compare a.w b.w |> function 0 -> Z.compare a.v b.v | o -> o

  let create ~(width : int) (v : Z.t) : t =
    assert (width >= 0);
    let v = z_extract v 0 width in
    { w = width; v }

  let of_int ~(width : int) i =
    assert (width > 0);
    let v = Z.of_int i in
    assert (Z.gt v (Z.of_int 0));
    create ~width v

  let of_string i =
    let vty = String.split_on_char ':' i in
    let w, v =
      match vty with
      | [ v; ty ] -> (
          String.to_seq ty |> List.of_seq |> function
          | 'b' :: 'v' :: width ->
              let width =
                Z.of_string
                  (String.concat "" (List.map (fun i -> String.make 1 i) width))
                |> Z.to_int
              in
              (width, Z.of_string v)
          | _ -> failwith "invalid format")
      | _ -> failwith "invalid format"
    in
    { w; v }

  let size_is_equal a b = assert (width a = width b)
  let bind f a = create ~width:a.w (f a.v)

  let bind2 f a b =
    size_is_equal a b;
    create ~width:a.w (f a.v b.v)

  let map2 f a b =
    size_is_equal a b;
    f a.v b.v

  let neg a = bind Z.neg a
  let add a b = bind2 Z.add a b
  let sub a b = bind2 Z.sub a b
  let bitnot a = bind Z.lognot a
  let bitand a b = bind2 Z.logand a b
  let bitor a b = bind2 Z.logor a b
  let bitxor a b = bind2 Z.logxor a b

  let udiv a b =
    size_is_equal a b;
    let v = if Z.equal b.v Z.zero then Z.minus_one else Z.div a.v b.v in
    create ~width:a.w v

  let sdiv a b =
    let neg_out = if is_negative a || is_negative b then neg else identity in
    let a = if is_negative a then neg a else a in
    let b = if is_negative b then neg b else b in
    neg_out (udiv a b)

  let urem a b = if is_zero b then a else bind2 Z.rem a b

  let srem a b =
    let neg_out = if is_negative a || is_negative b then neg else identity in
    let a = if is_negative a then neg a else a in
    let b = if is_negative b then neg b else b in
    neg_out (urem a b)

  let ult a b = map2 Z.lt a b
  let ugt a b = map2 Z.gt a b
  let ule a b = map2 Z.leq a b
  let uge a b = map2 Z.geq a b

  let map2_signed f a b =
    size_is_equal a b;
    f (to_signed_bigint a) (to_signed_bigint b)

  let slt a b = map2_signed Z.lt a b
  let sgt a b = map2_signed Z.gt a b
  let sle a b = map2_signed Z.leq a b
  let sge a b = map2_signed Z.geq a b
  let ashr a b = { w = a.w; v = Z.shift_right a.v (Z.to_int b.v) }
  let lshr a b = { w = a.w; v = Z.shift_right_trunc a.v (Z.to_int b.v) }
  let zero_extend ~(extension : int) b = { w = b.w + extension; v = b.v }

  let sign_extend ~(extension : int) b =
    let w = b.w + extension in
    let v = z_extract (z_signed_extract b.v 0 b.w) 0 w in
    { w; v }

  let concat a b =
    let a = zero_extend ~extension:b.w a in
    let a = { w = a.w; v = Z.shift_left a.v b.w } in
    let b = zero_extend ~extension:a.w b in
    bitor a b

  let repeat_bits ~(copies : int) a =
    List.init copies (fun _ -> a) |> List.fold_left concat empty
end

module BValue = struct
  type t =
    | Integer of PrimInt.t
    | Bitvector of PrimQFBV.t
    | Boolean of bool
    | Unit
  [@@deriving show, eq]

  let show = function
    | Integer i -> PrimInt.show i
    | Bitvector i -> PrimQFBV.show i
    | Boolean i -> Format.to_string Bool.pp i
    | Unit -> "()"

  let hash a =
    let open HashHelper in
    match a with
    | Integer i -> combine 2 (PrimInt.hash i)
    | Bitvector b -> combine 3 (PrimQFBV.hash b)
    | Boolean true -> combine 5 1
    | Boolean false -> combine 7 2
    | Unit as u -> Hashtbl.hash u
end
