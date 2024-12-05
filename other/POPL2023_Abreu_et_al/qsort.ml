
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
| True
| False

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type ('alg1, 'alg2) castAlg = __ -> 'alg1 -> 'alg2

type ('a, 'b, 'f) fmapT = ('a -> 'b) -> 'f -> 'f

type 'f functor0 =
  __ -> __ -> (__, __, 'f) fmapT
  (* singleton inductive, whose constructor was Build_Functor *)

(** val fmap : 'a1 functor0 -> ('a2, 'a3, 'a1) fmapT **)

let fmap functor1 f x =
  Obj.magic functor1 __ __ f x

type ('t, 'x) const = 't

(** val funConst : ('a1, __) const functor0 **)

let funConst _ _ _ xs =
  xs

type 'f mu =
| Mu of (__ -> 'f mu) * 'f

(** val inMu : 'a1 -> 'a1 mu **)

let inMu d =
  Mu ((fun x -> Obj.magic x), d)

(** val outMu : 'a1 functor0 -> 'a1 mu -> 'a1 **)

let outMu funF = function
| Mu (r, d) -> fmap funF r d

type ('f, 'x) muAlg =
| MuAlg of (__ -> __ -> ('f, __) muAlg) * 'f

(** val inMuAlg : 'a1 -> ('a1, 'a2) muAlg **)

let inMuAlg d =
  MuAlg ((fun _ x -> Obj.magic x), d)

(** val outMuAlg :
    (__ -> __ -> (__, __) castAlg -> ('a1, 'a1) castAlg) -> ('a1, 'a2) muAlg
    -> 'a1 **)

let outMuAlg algMap = function
| MuAlg (r, d) -> Obj.magic algMap __ __ r __ d

type ('alg, 'c) foldT = __ -> __ functor0 -> 'alg -> 'c -> __

type ('f, 'a, 'x) sAlgF =
  __ -> __ -> (__ -> __) -> ('a, __) foldT -> ('f -> __) -> (__ -> 'x) -> 'f
  -> 'x

type ('f, 'x) sAlg = (('f, __, __) sAlgF, 'x) muAlg

(** val monoSAlg :
    ('a2, 'a3) castAlg -> ('a1, 'a2, 'a4) sAlgF -> ('a6 -> 'a5) -> ('a3, 'a6)
    foldT -> ('a1 -> 'a5) -> ('a6 -> 'a4) -> 'a1 -> 'a4 **)

let monoSAlg castSAlg salgf cRS sfo =
  Obj.magic salgf __ __ cRS (fun _ xmap y -> sfo __ xmap (castSAlg __ y))

(** val rollSAlg : ('a1, ('a1, __) sAlg, 'a2) sAlgF -> ('a1, 'a2) sAlg **)

let rollSAlg d =
  inMuAlg (Obj.magic d)

(** val unrollSAlg :
    ('a1, 'a2) sAlg -> ('a4 -> 'a3) -> (('a1, __) sAlg, 'a4) foldT -> ('a1 ->
    'a3) -> ('a4 -> 'a2) -> 'a1 -> 'a2 **)

let unrollSAlg d up sfo abstIn rec0 d0 =
  outMuAlg (Obj.magic (fun _ _ x _ x0 _ _ -> monoSAlg x x0)) (Obj.magic d) __
    __ up sfo abstIn rec0 d0

type ('f, 'a, 'x) algF =
  __ -> ('a, __) foldT -> (('f, __) sAlg, __) foldT -> (__ -> 'x) -> 'f -> 'x

type ('f, 'x) alg = (('f, __, __) algF, 'x) muAlg

(** val monoAlg :
    ('a2, 'a3) castAlg -> ('a1, 'a2, 'a4) algF -> ('a3, 'a5) foldT -> (('a1,
    __) sAlg, 'a5) foldT -> ('a5 -> 'a4) -> 'a1 -> 'a4 **)

let monoAlg f algf fo =
  Obj.magic algf __ (fun _ xmap alg0 -> fo __ xmap (f __ alg0))

(** val rollAlg : ('a1, ('a1, __) alg, 'a2) algF -> ('a1, 'a2) alg **)

let rollAlg d =
  inMuAlg (Obj.magic d)

(** val unrollAlg :
    ('a1, 'a2) alg -> (('a1, __) alg, 'a3) foldT -> (('a1, __) sAlg, 'a3)
    foldT -> ('a3 -> 'a2) -> 'a1 -> 'a2 **)

let unrollAlg d fo sfo rec0 d0 =
  outMuAlg (Obj.magic (fun _ _ x _ x0 _ -> monoAlg x x0)) (Obj.magic d) __ fo
    sfo rec0 d0

type ('f, 'c) dcF = __ -> __ functor0 -> ('f, __) alg -> __

type 'f dc = ('f, __) dcF mu

(** val fmapDc :
    ('a2 -> 'a3) -> ('a1, 'a2) dcF -> 'a4 functor0 -> ('a1, 'a4) alg -> 'a4 **)

let fmapDc f initA xmap alg0 =
  fmap xmap f (Obj.magic initA __ xmap alg0)

(** val initFunc : ('a1, __) dcF functor0 **)

let initFunc _ _ x x0 _ =
  fmapDc x x0

(** val rollDc : ('a1, 'a1 dc) dcF -> 'a1 dc **)

let rollDc =
  inMu

(** val unrollDc : 'a1 dc -> 'a2 functor0 -> ('a1, 'a2) alg -> 'a2 **)

let unrollDc x funX x0 =
  outMu (Obj.magic initFunc) (Obj.magic x) __ funX x0

(** val fold : 'a2 functor0 -> ('a1, 'a2) alg -> 'a1 dc -> 'a2 **)

let fold funX alg0 d =
  unrollDc d funX alg0

type ('f, 'x, 'x0) revealT = ('x0 -> 'f dc) -> 'x

(** val revealFmap :
    'a2 functor0 -> ('a3 -> 'a4) -> ('a1, 'a2, 'a3) revealT -> ('a1, 'a2,
    'a4) revealT **)

let revealFmap _ f xs reveal =
  xs (fun a -> reveal (f a))

(** val funRevealT : 'a2 functor0 -> ('a1, 'a2, __) revealT functor0 **)

let funRevealT fun0 _ _ =
  revealFmap fun0

(** val promote :
    'a2 functor0 -> ('a1, 'a2) sAlg -> ('a1, ('a1, 'a2, __) revealT) alg **)

let promote funX salg =
  rollAlg (fun _ fo sfo _ fr reveal ->
    unrollSAlg salg reveal sfo (fun fr0 ->
      rollDc (fun _ funX0 alg0 ->
        fmap funX0 reveal (unrollAlg alg0 fo sfo (fo __ funX0 alg0) fr0)))
      (Obj.magic sfo __ funX salg) fr)

(** val sfold : 'a2 functor0 -> ('a1, 'a2) sAlg -> 'a1 dc -> 'a2 **)

let sfold funX salg x =
  fold (Obj.magic funRevealT funX) (Obj.magic promote funX salg) x (fun x0 ->
    x0)

(** val inDc : 'a1 -> 'a1 dc **)

let inDc d =
  rollDc (fun _ xmap alg0 ->
    unrollAlg alg0 (fun _ -> fold) (fun _ -> sfold) (fold xmap alg0) d)

type ('a, 'x) listF =
| Nil0
| Cons0 of 'a * 'x

type 'a list0 = ('a, __) listF dc

type ('a, 'r) listSFoldT = ((('a, __) listF, __) sAlg, 'r) foldT

(** val toList : 'a1 list -> ('a1, __) listF dc **)

let rec toList = function
| Nil -> inDc Nil0
| Cons (a, t0) -> Obj.magic inDc (Cons0 (a, (toList t0)))

type ('a, 'x) listAlg = (('a, __) listF, 'x) alg

type ('a, 'x) listSAlg = (('a, __) listF, 'x) sAlg

type ('a, 'x) partitionF = 'a -> ('x, 'x) prod

(** val partitionFmap :
    ('a2 -> 'a3) -> ('a1, 'a2) partitionF -> ('a1, 'a3) partitionF **)

let partitionFmap c f bound =
  let r = f bound in Pair ((c (fst r)), (c (snd r)))

(** val funPartitionF : ('a1, __) partitionF functor0 **)

let funPartitionF _ _ =
  partitionFmap

(** val partitionSAlg :
    ('a1 -> 'a1 -> bool) -> ('a1, ('a1, __) partitionF) listSAlg **)

let partitionSAlg ltA =
  rollSAlg (fun _ _ up _ abstIn rec0 d bound ->
    match d with
    | Nil0 -> Pair ((abstIn d), (abstIn d))
    | Cons0 (x, xs) ->
      let Pair (l, r) = rec0 xs bound in
      (match ltA x bound with
       | True -> Pair ((abstIn (Cons0 (x, l))), (up r))
       | False -> Pair ((up l), (abstIn (Cons0 (x, r))))))

(** val partitionr :
    ('a1 -> 'a1 -> bool) -> ('a1, 'a2) listSFoldT -> 'a2 -> 'a1 -> ('a2, 'a2)
    prod **)

let partitionr ltA sfo l bound =
  Obj.magic sfo __ funPartitionF (partitionSAlg ltA) l bound

(** val partitionr0 :
    ('a1 -> 'a1 -> bool) -> ('a1, 'a2) listSFoldT -> 'a2 -> 'a1 -> ('a2, 'a2)
    prod **)

let partitionr0 =
  partitionr

(** val quicksortAlg :
    ('a1 -> 'a1 -> bool) -> ('a1, ('a1 list, __) const) listAlg **)

let quicksortAlg ltA =
  rollAlg (fun _ _ sfo qsort xs ->
    match xs with
    | Nil0 -> Nil
    | Cons0 (p, xs0) ->
      let Pair (l, r) = partitionr0 ltA sfo xs0 p in
      app (qsort l) (Cons (p, (qsort r))))

(** val quicksort : ('a1 -> 'a1 -> bool) -> 'a1 list0 -> 'a1 list **)

let quicksort ltA l =
  fold funConst (quicksortAlg ltA) l

(** val quicksort0 : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let quicksort0 ltA l =
  quicksort ltA (toList l)
