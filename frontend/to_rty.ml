module MetaEnv = Env

let layout rty = To_pty.layout @@ Pty.rty_to_pty rty

let rty_of_ocamlexpr expr =
  let pty = To_pty.pty_of_ocamlexpr expr in
  let rty = Pty.pty_to_rty pty in
  let _ =
    Env.show_debug_kw __FILE__ (fun _ ->
        Printf.printf "pty to rty: %s ====> %s\n" (To_pty.layout pty)
          (To_pty.layout @@ Pty.raw_rty_to_pty rty))
  in
  rty
