open Langlike

module StrId = struct
  type t = string

  let equal = String.equal
  let layout x = x
end

module OpId = struct
  type t = Op.t

  let equal = Op.eq
  let layout = Op.to_string
end

module F (I : BindingName) (E : Layoutable) = struct
  open Zzdatatype.Datatype
  open Sugar

  type t = (I.t * E.t) list

  let last_destruct_opt = List.last_destruct_opt
  let layout_binding (x, ty) = spf "%s:%s" (I.layout x) (E.layout ty)
  let layout = Zzdatatype.Datatype.List.split_by_comma layout_binding
  let from_kv_list l = l
  let empty = []
  let exists ctx name = List.exists (fun (x, _) -> I.equal x name) ctx

  let find_opt ctx id : E.t option =
    match List.find_opt (fun (x, _) -> I.equal id x) ctx with
    | None -> None
    | Some (_, ty) -> Some ty

  let find ctx id : E.t =
    match find_opt ctx id with
    | None ->
        _failatwith __FILE__ __LINE__
        @@ spf "no such name (%s) in the type context" (I.layout id)
    | Some ty -> ty

  let new_to_right ctx (x, ty) =
    if exists ctx x then
      _failatwith __FILE__ __LINE__ (spf "Add repeat binding %s" (I.layout x))
    else ctx @ [ (x, ty) ]

  let new_to_rights ctx l = List.fold_left new_to_right ctx l
  let fold_right = List.fold_right
  let fold_left = List.fold_left
  let filter_map = List.filter_map

  let update ctx (id, tau) =
    List.filter_map
      (fun (id', tau') ->
        if I.equal id id' then Some (id, tau) else Some (id', tau'))
      ctx

  let pretty_layout ctx = List.split_by ", " layout_binding ctx

  let pretty_print ctx =
    Env.show_debug_typing (fun _ ->
        if List.length ctx == 0 then Pp.printf "@{<green>∅@}"
        else
          List.iter
            (fun (x, ty) ->
              Pp.printf "%s:@{<green>%s@}," (I.layout x) (E.layout ty))
            ctx)

  let pretty_print_lines ctx =
    Env.show_debug_typing (fun _ ->
        if List.length ctx == 0 then Pp.printf "@{<green>∅@}\n"
        else
          List.iter
            (fun (x, ty) ->
              Pp.printf "%s:@{<green>%s@}\n" (I.layout x) (E.layout ty))
            ctx)

  let pretty_layout_subtyping ctx (r1, r2) =
    Env.show_debug_typing (fun _ ->
        let () = Pp.printf "@{<bold>Subtyping:@}\n" in
        pretty_print ctx;
        Pp.printf "⊢\n@{<hi_magenta>%s@} <:\n@{<cyan>%s@}\n" r1 r2)

  let pretty_print_infer ctx (e, r) =
    Env.show_debug_typing (fun _ ->
        let () = Pp.printf "@{<bold>Type Infer:@}\n" in
        pretty_print ctx;
        Pp.printf "⊢ @{<hi_magenta>%s@} ⇨ " (short_str 100 e);
        Pp.printf "@{<cyan>%s@}\n\n" @@ r)

  let pretty_print_judge ctx (e, r) =
    Env.show_debug_typing (fun _ ->
        let () = Pp.printf "@{<bold>Type Check:@}\n" in
        pretty_print ctx;
        Pp.printf "⊢ @{<hi_magenta>%s@} ⇦ " (short_str 10000 e);
        Pp.printf "@{<cyan>%s@}\n\n" r)
end

module FString (E : Layoutable) = struct
  include F (StrId) (E)
end

module FOp (E : Layoutable) = struct
  include F (OpId) (E)
end
