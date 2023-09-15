module MetaEnv = Env

let layout rty = To_pty.layout @@ Pty.rty_to_pty rty

let rty_of_ocamlexpr expr =
  let rty = Pty.pty_to_rty @@ To_pty.pty_of_ocamlexpr_aux expr in
  (* let rty = Syntax.RtyRaw.normalize_name rty in *)
  rty
