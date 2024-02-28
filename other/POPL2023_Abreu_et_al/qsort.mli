
type __ = Obj.t

type bool =
| True
| False

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

type ('alg1, 'alg2) castAlg = __ -> 'alg1 -> 'alg2

type ('a, 'b, 'f) fmapT = ('a -> 'b) -> 'f -> 'f

type 'f functor0 =
  __ -> __ -> (__, __, 'f) fmapT
  (* singleton inductive, whose constructor was Build_Functor *)

val fmap : 'a1 functor0 -> ('a2, 'a3, 'a1) fmapT

type ('t, 'x) const = 't

val funConst : ('a1, __) const functor0

type 'f mu =
| Mu of (__ -> 'f mu) * 'f

val inMu : 'a1 -> 'a1 mu

val outMu : 'a1 functor0 -> 'a1 mu -> 'a1

type ('f, 'x) muAlg =
| MuAlg of (__ -> __ -> ('f, __) muAlg) * 'f

val inMuAlg : 'a1 -> ('a1, 'a2) muAlg

val outMuAlg :
  (__ -> __ -> (__, __) castAlg -> ('a1, 'a1) castAlg) -> ('a1, 'a2) muAlg ->
  'a1

type ('alg, 'c) foldT = __ -> __ functor0 -> 'alg -> 'c -> __

type ('f, 'a, 'x) sAlgF =
  __ -> __ -> (__ -> __) -> ('a, __) foldT -> ('f -> __) -> (__ -> 'x) -> 'f
  -> 'x

type ('f, 'x) sAlg = (('f, __, __) sAlgF, 'x) muAlg

val monoSAlg :
  ('a2, 'a3) castAlg -> ('a1, 'a2, 'a4) sAlgF -> ('a6 -> 'a5) -> ('a3, 'a6)
  foldT -> ('a1 -> 'a5) -> ('a6 -> 'a4) -> 'a1 -> 'a4

val rollSAlg : ('a1, ('a1, __) sAlg, 'a2) sAlgF -> ('a1, 'a2) sAlg

val unrollSAlg :
  ('a1, 'a2) sAlg -> ('a4 -> 'a3) -> (('a1, __) sAlg, 'a4) foldT -> ('a1 ->
  'a3) -> ('a4 -> 'a2) -> 'a1 -> 'a2

type ('f, 'a, 'x) algF =
  __ -> ('a, __) foldT -> (('f, __) sAlg, __) foldT -> (__ -> 'x) -> 'f -> 'x

type ('f, 'x) alg = (('f, __, __) algF, 'x) muAlg

val monoAlg :
  ('a2, 'a3) castAlg -> ('a1, 'a2, 'a4) algF -> ('a3, 'a5) foldT -> (('a1,
  __) sAlg, 'a5) foldT -> ('a5 -> 'a4) -> 'a1 -> 'a4

val rollAlg : ('a1, ('a1, __) alg, 'a2) algF -> ('a1, 'a2) alg

val unrollAlg :
  ('a1, 'a2) alg -> (('a1, __) alg, 'a3) foldT -> (('a1, __) sAlg, 'a3) foldT
  -> ('a3 -> 'a2) -> 'a1 -> 'a2

type ('f, 'c) dcF = __ -> __ functor0 -> ('f, __) alg -> __

type 'f dc = ('f, __) dcF mu

val fmapDc :
  ('a2 -> 'a3) -> ('a1, 'a2) dcF -> 'a4 functor0 -> ('a1, 'a4) alg -> 'a4

val initFunc : ('a1, __) dcF functor0

val rollDc : ('a1, 'a1 dc) dcF -> 'a1 dc

val unrollDc : 'a1 dc -> 'a2 functor0 -> ('a1, 'a2) alg -> 'a2

val fold : 'a2 functor0 -> ('a1, 'a2) alg -> 'a1 dc -> 'a2

type ('f, 'x, 'x0) revealT = ('x0 -> 'f dc) -> 'x

val revealFmap :
  'a2 functor0 -> ('a3 -> 'a4) -> ('a1, 'a2, 'a3) revealT -> ('a1, 'a2, 'a4)
  revealT

val funRevealT : 'a2 functor0 -> ('a1, 'a2, __) revealT functor0

val promote :
  'a2 functor0 -> ('a1, 'a2) sAlg -> ('a1, ('a1, 'a2, __) revealT) alg

val sfold : 'a2 functor0 -> ('a1, 'a2) sAlg -> 'a1 dc -> 'a2

val inDc : 'a1 -> 'a1 dc

type ('a, 'x) listF =
| Nil0
| Cons0 of 'a * 'x

type 'a list0 = ('a, __) listF dc

type ('a, 'r) listSFoldT = ((('a, __) listF, __) sAlg, 'r) foldT

val toList : 'a1 list -> ('a1, __) listF dc

type ('a, 'x) listAlg = (('a, __) listF, 'x) alg

type ('a, 'x) listSAlg = (('a, __) listF, 'x) sAlg

type ('a, 'x) partitionF = 'a -> ('x, 'x) prod

val partitionFmap :
  ('a2 -> 'a3) -> ('a1, 'a2) partitionF -> ('a1, 'a3) partitionF

val funPartitionF : ('a1, __) partitionF functor0

val partitionSAlg :
  ('a1 -> 'a1 -> bool) -> ('a1, ('a1, __) partitionF) listSAlg

val partitionr :
  ('a1 -> 'a1 -> bool) -> ('a1, 'a2) listSFoldT -> 'a2 -> 'a1 -> ('a2, 'a2)
  prod

val partitionr0 :
  ('a1 -> 'a1 -> bool) -> ('a1, 'a2) listSFoldT -> 'a2 -> 'a1 -> ('a2, 'a2)
  prod

val quicksortAlg : ('a1 -> 'a1 -> bool) -> ('a1, ('a1 list, __) const) listAlg

val quicksort : ('a1 -> 'a1 -> bool) -> 'a1 list0 -> 'a1 list

val quicksort0 : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
