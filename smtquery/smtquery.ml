exception FailWithModel of string * Z3.Model.model

let _failwithmodel file line msg model =
  raise (FailWithModel (Printf.sprintf "[%s:%i] %s" file line msg, model))

let ctx =
  Z3.mk_context
    [ ("model", "true"); ("proof", "false"); ("timeout", "9999999") ]

let _check pre q =
  Check.(handle_check_res (fun () -> smt_neg_and_solve ctx pre q))

let check_with_pre pres vc = _check pres vc

(* let check_implies_with_pre pres a b = *)
(*   _check pres Language.Rty.P.(Implies (a, b)) *)

let check vc = check_with_pre [] vc
let cache_size = 600
let check_bool_cache = Hashtbl.create cache_size

let layout_cache cache =
  let counters = List.map snd @@ List.of_seq @@ Hashtbl.to_seq_values cache in
  let counters, l = List.partition (fun x -> x > 1) counters in
  Printf.sprintf "%s\n(hit: %i, miss: %i)\n"
    (Zzdatatype.Datatype.IntList.to_string counters)
    (List.length counters) (List.length l)

let cached (cache : ('a, bool * int) Hashtbl.t) (check : 'a -> bool) (vc : 'a) =
  if Hashtbl.length cache >= cache_size - 1 then check vc
  else
    match Hashtbl.find_opt cache vc with
    | Some (result, counter) ->
        Hashtbl.replace cache vc (result, counter + 1);
        result
    | None ->
        let res = check vc in
        Hashtbl.add cache vc (res, 1);
        res

let check_bool vc =
  let runtime, res = Sugar.clock (fun () -> check vc) in
  let () =
    Env.show_debug_stat @@ fun _ -> Printf.printf "check_bool: %f\n" runtime
  in
  match res with
  | None -> true
  | Some _ ->
      (* | Some model -> *)
      (* ( Env.show_debug_queries @@ fun _ -> *)
      (*   Printf.printf "model:\n%s\n" (Z3.Model.to_string model) ); *)
      false

let cached_check_bool vc = cached check_bool_cache check_bool vc
(* let check_implies a b = check_implies_with_pre [] a b *)

(* let check_implies_bool (a, b) = *)
(*   match check_implies a b with None -> true | Some _ -> false *)

let stat_init = Check.stat_init
let stat_get_cur = Check.stat_get_cur
let test0 () = ()
