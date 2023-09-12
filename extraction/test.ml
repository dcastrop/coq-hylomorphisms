
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

type ('sh, 'p) elem_of = 'p

type 'a ts =
| Leaf
| Node of 'a

type tp =
| Lbranch
| Rbranch

(** val dom_leaf : ('a1 ts, tp) elem_of -> 'a2 **)

let dom_leaf _ =
  assert false (* absurd case *)

(** val msort : int list -> int list **)

let rec msort = function
| [] ->
  let s_x = Leaf in
  let k = fun e -> msort (dom_leaf e) in
  (match s_x with
   | Leaf -> []
   | Node x0 -> let p = ((x0, (k Lbranch)), (k Rbranch)) in let (p0, r) = p in let (h, l) = p0 in app l (h :: r))
| h :: t ->
  let s_x = Node h in
  let c_x = fun p ->
    match p with
    | Lbranch -> filter (fun x0 -> (<=) x0 h) t
    | Rbranch -> filter (fun x0 -> negb ((<=) x0 h)) t
  in
  let k = fun e -> msort (c_x e) in
  (match s_x with
   | Leaf -> []
   | Node x0 -> let p = ((x0, (k Lbranch)), (k Rbranch)) in let (p0, r) = p in let (h0, l) = p0 in app l (h0 :: r))
