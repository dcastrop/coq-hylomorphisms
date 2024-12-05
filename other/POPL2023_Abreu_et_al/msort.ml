
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type ('a, 'b) prod =
| Pair of 'a * 'b

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

(** val out : 'a1 functor0 -> (('a1, __) sAlg, 'a2) foldT -> 'a2 -> 'a1 **)

let out funF sfo =
  Obj.magic sfo __ funF (rollSAlg (fun _ _ up _ _ _ d -> fmap funF up d))

(** val inDc : 'a1 -> 'a1 dc **)

let inDc d =
  rollDc (fun _ xmap alg0 ->
    unrollAlg alg0 (fun _ -> fold) (fun _ -> sfold) (fold xmap alg0) d)

type ('a, 'x) listF =
| Nil0
| Cons0 of 'a * 'x

(** val funListF : ('a1, __) listF functor0 **)

let funListF _ _ f = function
| Nil0 -> Nil0
| Cons0 (a, l) -> Cons0 (a, (f l))

type 'a list0 = ('a, __) listF dc

(** val toList : 'a1 list -> ('a1, __) listF dc **)

let rec toList = function
| Nil -> inDc Nil0
| Cons (a, t0) -> Obj.magic inDc (Cons0 (a, (toList t0)))

(** val fromListr :
    ((('a1, __) listF, __) alg, 'a2) foldT -> 'a2 -> 'a1 list **)

let fromListr fo x =
  Obj.magic fo __ funConst
    (rollAlg (fun _ _ _ rec0 fr ->
      match fr with
      | Nil0 -> Nil
      | Cons0 (a, l) -> Cons (a, (rec0 l)))) x

type ('a, 'x) listAlg = (('a, __) listF, 'x) alg

type ('a, 'x) listSAlg = (('a, __) listF, 'x) sAlg

type 'x splitF = ('x, 'x) prod

(** val splitFmap : ('a1 -> 'a2) -> 'a1 splitF -> 'a2 splitF **)

let splitFmap f = function
| Pair (a1, a2) -> Pair ((f a1), (f a2))

(** val funSplitF : __ splitF functor0 **)

let funSplitF _ _ =
  splitFmap

(** val splitAlg : ('a1, __ splitF) listSAlg **)

let splitAlg =
  rollSAlg (fun _ _ _ sfo abstIn split xs ->
    match xs with
    | Nil0 -> Pair ((abstIn Nil0), (abstIn Nil0))
    | Cons0 (hd, tl) ->
      (match out funListF sfo tl with
       | Nil0 -> Pair ((abstIn (Cons0 (hd, tl))), (abstIn Nil0))
       | Cons0 (hd', tl') ->
         let Pair (ys, zs) = split tl' in
         Pair ((abstIn (Cons0 (hd, ys))), (abstIn (Cons0 (hd', zs))))))

(** val mTestAlg : ('a1, ('a1 -> 'a1 list, __) const) listAlg **)

let mTestAlg =
  rollAlg (fun _ fo sfo _ xs a ->
    match xs with
    | Nil0 -> Cons (a, Nil)
    | Cons0 (hd, tl) ->
      let Pair (ys, zs) = Obj.magic sfo __ funSplitF splitAlg tl in
      app (Cons (a, (fromListr fo ys))) (Cons (hd, (fromListr fo zs))))

(** val mtesth : 'a1 list0 -> 'a1 -> 'a1 list **)

let mtesth xs x =
  fold funConst mTestAlg xs x

(** val mtest : 'a1 list -> 'a1 list **)

let mtest = function
| Nil -> Nil
| Cons (hd, tl) -> mtesth (toList tl) hd
