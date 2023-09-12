
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

type tp =
| Lbranch
| Rbranch

(** val msort : int list -> int list **)

let rec msort = function
| [] -> []
| h :: t ->
  let k = fun e ->
    msort
      (match e with
       | Lbranch -> filter (fun x0 -> (<=) x0 h) t
       | Rbranch -> filter (fun x0 -> negb ((<=) x0 h)) t)
  in
  app (k Lbranch) (h :: (k Rbranch))
