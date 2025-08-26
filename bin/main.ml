
open Lang.Ast_sandbox

let f x = `BvAdd (x, x)

module Closed = Close(AllOps)

let () =
  print_endline "Hello, World!";
  print_endline @@ Int.to_string @@ AllOps.depth_allops @@ f (f (`IntLit 2));
  print_endline @@ Closed.(show @@ fix @@ f (fix @@ `IntLit 2))
