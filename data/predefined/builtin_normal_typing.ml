(** builtin operators *)
val ( == ) : int -> int -> bool
val ( != ) : int -> int -> bool
val ( < ) : int -> int -> bool
val ( <= ) : int -> int -> bool
val ( > ) : int -> int -> bool
val ( >= ) : int -> int -> bool
val ( + ) : int -> int -> int
val ( - ) : int -> int -> int
val ( mod ) : int -> int -> int
val ( * ) : int -> int -> int
val ( / ) : int -> int -> int
(** datatype constructors *)
val _Nil : int list
val _Cons : int -> int list -> int list
(** method predicates *)
val size : int list -> int
val mem : int list -> int -> bool
val set_rep : int list -> bool
(* val hd : int list -> int -> bool *)
(* val tl : int list -> int list -> bool *)
