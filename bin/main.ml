open Cmdliner
open Lang.Prog

let () = Printexc.record_backtrace true

let check fname proc =
  let p = Ocaml_of_basil.Loadir.ast_of_fname fname in
  let procs prog =
    let open Program in
    ID.Map.iter
      (fun i (_ : Procedure.t) ->
        Printf.printf "%d %s\n" i (prog.proc_names.get_name i))
      prog.procs
  in
  if proc <> "" then
    let id = p.prog.proc_names.get_id proc in
    let p = ID.Map.find id p.prog.procs in
    Lang.Livevars.print_live_vars_dot Format.std_formatter p
  else procs p.prog

let fname =
  let doc = "Input file name (filename.il)" in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"FNAME" ~doc)

let proc =
  let doc = "proc to output" and docv = "PROC" in
  Arg.(value & opt string "" & info [ "p"; "proc" ] ~doc ~docv)

let check_f = Term.(const check $ fname $ proc)

let cmd =
  let doc = "obasil" in
  let info = Cmd.info "obasil" ~version:"alpha" ~doc in
  Cmd.v info check_f

let main () = exit (Cmd.eval cmd)
let () = main ()
