
val negb : bool -> bool

val app : 'a1 list -> 'a1 list -> 'a1 list

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

type tp =
| Lbranch
| Rbranch

val msort : int list -> int list
