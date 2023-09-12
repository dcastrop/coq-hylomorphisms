
val negb : bool -> bool

val app : 'a1 list -> 'a1 list -> 'a1 list

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

type ('sh, 'p) elem_of = 'p

type 'a ts =
| Leaf
| Node of 'a

type tp =
| Lbranch
| Rbranch

val dom_leaf : ('a1 ts, tp) elem_of -> 'a2

val msort : int list -> int list
