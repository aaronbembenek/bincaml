open Containers
open Lang
open Prog

let print_proc chan p =
  let p =
    Lang.Prog.Procedure.pretty Lang.Var.to_string Lang.Expr.BasilExpr.to_string
      p
  in
  output_string chan @@ Containers_pp.Pretty.to_string ~width:80 p

let assert_atoms n args =
  assert (List.length args = n);
  List.map (function `Atom n -> n | _ -> failwith "expected atom") args

type dsl_st = { prog : Program.t option }

let init_st = { prog = None }
let get_prog s = Option.get_exn_or "no program loaded" s.prog

let of_cmd st (e : Containers.Sexp.t) =
  let cmd, args =
    match e with
    | `List (`Atom cmd :: n) -> (cmd, n)
    | _ -> failwith "bad cmd structure"
  in
  match cmd with
  | "load-il" ->
      let fname = List.hd (assert_atoms 1 args) in
      let p = Ocaml_of_basil.Loadir.ast_of_fname fname in
      { st with prog = Some p.prog }
  | "dump-proc-il" ->
      let proc = List.hd (assert_atoms 1 args) in
      let id = (get_prog st).proc_names.get_id proc in
      let p = Lang.ID.Map.find id (get_prog st).procs in
      print_proc stdout p;
      st
  | "write-proc-il" ->
      let proc, ofile =
        assert_atoms 2 args |> function
        | [ proc; ofile ] -> (proc, ofile)
        | _ -> failwith "unreachable"
      in
      CCIO.with_out ofile (fun c ->
          let id = (get_prog st).proc_names.get_id proc in
          let p = Lang.ID.Map.find id (get_prog st).procs in
          print_proc c p);
      st
  | "run-transforms" ->
      let args = assert_atoms (List.length args) args in
      let ba = Ocaml_of_basil.Passes.PassManager.batch_of_list args in
      Ocaml_of_basil.Passes.PassManager.run_batch ba (get_prog st);
      st
  | "run-transform" ->
      let args = assert_atoms 1 args in
      let ba = Ocaml_of_basil.Passes.PassManager.batch_of_list args in
      Ocaml_of_basil.Passes.PassManager.run_batch ba (get_prog st);
      st
  | e -> failwith @@ "not a command : " ^ e

let of_str st (e : string) =
  let s = CCSexp.parse_string e in
  let s = Result.get_exn s in
  of_cmd st s
