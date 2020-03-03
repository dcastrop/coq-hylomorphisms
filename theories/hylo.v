From mathcomp Require Import all_ssreflect.
From Paco Require Import paco paco2.
Require Import Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "x =l y" (at level 70, no associativity).
Reserved Notation "x =g y" (at level 70, no associativity).
Reserved Notation "x =a/g y" (at level 70, no associativity).
Reserved Notation "x '=1/g' y" (at level 70, no associativity).
Reserved Notation "x '=1/a' y" (at level 70, no associativity).
Reserved Notation "x '=1/a/g' y" (at level 70, no associativity).
Reserved Notation "x '=1/sval' y" (at level 70, no associativity).

(****************************************************************************)
(** Assumptions and Strict positivisation of functors                      **)
(****************************************************************************)
Class equivalence A : Type :=
  MkEquiv
    { eqRel : A -> A -> Prop;
      e_refl : forall x, eqRel x x;
      e_sym : forall x y, eqRel x y -> eqRel y x;
      e_trans : forall x y z, eqRel x y -> eqRel y z -> eqRel x z;
    }.

Hint Resolve e_refl : ffix.
Hint Resolve e_sym : ffix.
Hint Resolve e_trans : ffix.

(* Instance def_eq A : equivalence A := *)
(*   {| eqRel := @eq A; *)
(*      e_refl := @erefl A; *)
(*      e_sym := @esym A; *)
(*      e_trans := @etrans A; *)
(*   |}. *)


Add Parametric Relation (A: Type) (eq : equivalence A) : A (@eqRel A eq)
    reflexivity proved by (@e_refl A eq)
    symmetry proved by (@e_sym A eq)
    transitivity proved by (@e_trans A eq)
      as ExtEq.

Reserved Notation "f =e g" (at level 70, no associativity).
(* Reserved Notation "f =1e g" (at level 70, no associativity). *)
Notation "f =e g" := (eqRel f g).
(* Notation "f =1e g" := (forall x, eqRel (Eq _) (f x) (g x)). *)

Instance ext_eq (A B : Type) (eq_B : equivalence B) : equivalence (A -> B).
Proof.
  apply: (@MkEquiv _ (fun f g =>forall x, eqRel (f x) (g x))).
  - by move=>f x; apply: e_refl.
  - by move=>f g H x; apply: e_sym.
  - by move=>f g h Hf Hg x; apply: e_trans.
Defined.

(** Is position valid in shape? *)
Class functor (S P : Type) :=
  { dom : S -> P -> bool
  }.

Definition App S P {F : functor S P} (X : Type) := {sh : S & sig (dom sh) -> X}.
Arguments App S P [F] X.

Lemma cont_irr S P {F : functor S P} X (sh : S) (f : sig (dom sh) -> X)
  : forall x p1 p2, f (exist _ x p1) = f (exist _ x p2).
Proof. move=> x/= p1 p2; by rewrite (bool_irrelevance p1 p2). Qed.

Definition AppR S P {F : functor S P} (X : Type) {e : equivalence X}
           (x y : App S P X) : Prop
  := projT1 x = projT1 y /\
     (forall e d1 d2, projT2 x (exist _ e d1) =e projT2 y (exist _ e d2)).

Lemma AppR_inv_sh S P {F : functor S P} X {e : equivalence X} x y :
  AppR x y -> projT1 x = projT1 y.
Proof. by case. Qed.

Lemma AppR_inv_k S P {F : functor S P} X {e : equivalence X} x y :
  AppR x y ->
  forall e d1 d2, projT2 x (exist _ e d1) =e projT2 y (exist _ e d2).
Proof. by case. Qed.

Instance App_equiv S P {F : functor S P} (X : Type) {e : equivalence X}
  : equivalence (App S P X).
Proof.
  apply: (@MkEquiv _ (@AppR S P F X e)).
  - move=> [shx kx]; constructor=>//=x d1 d2.
    rewrite (bool_irrelevance d1 d2); by apply: e_refl.
  - move=> x y [Sxy Exy]; split; first by apply/esym.
    by move=> z d1 d2; symmetry.
  - move=> x y z [Sxy Exy] [Syz Eyz]; split; first by rewrite Sxy.
    move=>t d1 d2; have d3: dom (projT1 y) t by move: d1; rewrite Sxy.
    by rewrite (Exy t d1 d3).
Defined.

Structure morph (A B : Type) {eq_A : equivalence A} {eq_B : equivalence B}
  := { app :> A -> B;
       f_eq : forall x y, x =e y -> app x =e app y
     }.
Arguments morph A B _ _ : clear implicits.

Reserved Notation "x ~> y" (at level 95, right associativity, y at level 200).
Notation "x ~> y" := (morph x y _ _).

Instance eq_morph (A B : Type) {eq_A : equivalence A} {eq_B : equivalence B}
  : equivalence (A ~> B).
Proof.
  apply: (@MkEquiv _ (fun f g =>forall x, app f x =e app g x)).
  - by move=>f x; apply: e_refl.
  - by move=>f g H x; apply: e_sym.
  - by move=>f g h Hf Hg x; apply: e_trans.
Defined.

(* Definition arr (A B : Type) (eq_A : equivalence A) (eq_B : equivalence B) *)
(*   := sig (@morph A B eq_A eq_B). *)

Definition fmapA S P {F : functor S P} A B (f : A -> B) (x : App S P A)
  : App S P B := existT _ (projT1 x) (f \o projT2 x).

Lemma fmapA_eqF S P {F : functor S P} A B
      {eq_A : equivalence A} {eq_B : equivalence B}
      (f : A ~> B)
  : forall x y, x =e y -> fmapA f x =e fmapA f y.
Proof.
  move=> [sx kx] [sy ky] [/=Es Ek]; split=>//= e d1 d2.
  by apply/f_eq/Ek.
Qed.

Definition fmap S P {F : functor S P}
           A B {eq_A : equivalence A} {eq_B : equivalence B}
           (f : A ~> B) : App S P A ~> App S P B
  := {| app := _ ; f_eq := fmapA_eqF f |}.

Lemma comp_eq A B C
      {e1 : equivalence A} {e2 : equivalence B} {e3 : equivalence C}
      (f : B ~> C) (g : A ~> B) :
  forall x y, x =e y -> (f \o g) x =e (f \o g) y.
Proof. by move=> x y H; apply/f_eq/f_eq. Qed.

Definition acomp A B C
      {e1 : equivalence A} {e2 : equivalence B} {e3 : equivalence C}
      (f : B ~> C) (g : A ~> B) : A ~> C
  := {| app := _; f_eq := comp_eq f g |}.

Notation "f \o g" := (acomp f g).

Lemma id_eq (A : Type) {eq_A : equivalence A}
  : forall (x y : A), x =e y -> id x =e id y.
Proof. by []. Qed.

Definition id A {eq : equivalence A} : A ~> A :=
  {| app := _; f_eq := @id_eq A eq |}.
Arguments id {A eq}.

Lemma fmap_id S P {F : functor S P} A {eq_A : equivalence A}
  : fmap (S:=S) (P:=P) (A:=A) id =e id.
Proof.
  move=> [s k]/=; rewrite /fmap/=; split=>//= e d1 d2.
  rewrite (bool_irrelevance d2 d1); by reflexivity.
Qed.

Lemma fmap_comp S P {F : functor S P} (A B C : Type)
      {eq_A : equivalence A} {eq_B : equivalence B} {eq_C :equivalence C}
      (f : B ~> C) (g : A ~> B)
  : fmap (f \o g) =e fmap f \o fmap g.
Proof.
  move=> [s k]/=; rewrite /fmap/=; split=>//= e d1 d2.
  rewrite (bool_irrelevance d2 d1); by reflexivity.
Qed.

Add Parametric Morphism S P (F : functor S P)
    (A B : Type) (e1 : equivalence A) (e2 : equivalence B)
  : (@fmap S P F A B e1 e2)
    with signature
    (eqRel (A:=A ~> B))
      ==> (eqRel (A:=App S P A ~> App S P B))
      as fmapMorphism.
Proof.
  move=> f1 f2 Ef [s k]; split=>//= e d1 d2.
  by rewrite (bool_irrelevance d1 d2).
Qed.

Add Parametric Morphism (A B C : Type)
    (eA : equivalence A) (eB : equivalence B) (eC : equivalence C)
  : (@acomp A B C eA eB eC)
    with signature
    (eqRel (A:=B ~> C))
      ==> (eqRel (A:=A ~> B))
      ==> (eqRel (A:=A ~> C))
      as compMorphism.
Proof.
  move=> f1 f2 Ef g1 g2 Eg x=>//=.
  by apply/(e_trans (Ef (g1 x)))/f_eq/Eg.
Qed.

Definition Alg S P {F : functor S P} A {eA : equivalence A} := App S P A ~> A.
Arguments Alg S P {F} A {eA}.
Definition CoAlg S P {F : functor S P} A {eA : equivalence A} := A ~> App S P A.
Arguments CoAlg S P {F} A {eA}.

Inductive LFix S P {F : functor S P} : Type :=
| LFix_in sh : (sig (dom sh) -> @LFix S P F) -> @LFix S P F.
Arguments LFix S P {F}.

Definition l_shape S P {F : functor S P} (x : LFix S P) :=
  match x with
  | LFix_in sh _ => sh
  end.
Definition l_cont S P {F : functor S P} (x : LFix S P) :=
  match x return sig (dom (l_shape x)) -> LFix S P with
  | LFix_in _ k => k
  end.

Fixpoint LFixR S P {F : functor S P} (x y : LFix S P) : Prop :=
  l_shape x = l_shape y /\
  forall e d1 d2,
      LFixR (l_cont (x:=x) (exist _ e d1)) (l_cont (x:=y) (exist _ e d2)).

Lemma LFixR_inv_sh S P {F : functor S P} (x y : LFix S P)
  : LFixR x y -> l_shape x = l_shape y.
Proof. by case: x=>[sx kx]; case: y=>[sy ky] []. Qed.

Lemma LFixR_inv_k S P {F : functor S P} (x y : LFix S P)
  : LFixR x y ->
    forall e d1 d2,
      LFixR (l_cont (x:=x) (exist _ e d1)) (l_cont (x:=y) (exist _ e d2)).
Proof. by case: x=>[sx kx]; case: y=>[sy ky] []. Qed.

Lemma LFixR_refl S P {F : functor S P} (x : LFix S P) : LFixR x x.
Proof.
  elim: x=>// shx k Ih; constructor=>//=x p1 p2.
  by rewrite (bool_irrelevance p1 p2); apply: Ih.
Qed.

Lemma LFixR_sym S P {F : functor S P} (x y : LFix S P) : LFixR x y -> LFixR y x.
Proof.
  elim: x => sx kx Ih in y *; case: y => sy ky /=[/esym-Sxy E].
  split=>// e d1 d2; by apply/Ih/E.
Qed.

Lemma LFixR_trans S P {F : functor S P} (x y z : LFix S P)
  : LFixR x y -> LFixR y z -> LFixR x z.
Proof.
  elim: x=> sx kx Ih in y z *; case: y=> sy ky/=; case: z=> sz kz/=.
  move=> [Sxy Exy] [Syz Eyz]; split; first by rewrite Sxy.
  move=> e d1 d2; apply: Ih; first by apply: Exy; rewrite Syz.
  by apply/Eyz.
Qed.

Instance LFix_Eq S P {F : functor S P} : equivalence (LFix S P) :=
  {| eqRel := @LFixR S P F;
     e_refl := @LFixR_refl S P F;
     e_sym := @LFixR_sym S P F;
     e_trans := @LFixR_trans S P F;
  |}.

Definition l_in_f S P {F : functor S P} (x : App S P (LFix S P)) : LFix S P :=
  LFix_in (projT2 x).

Lemma l_in_eq S P {F : functor S P} x y : x =e y -> l_in_f x =e l_in_f y.
Proof. by case: x=> sx kx; case: y=> sy ky/= [/=Es Ek]; split. Qed.

Definition l_out_f S P {F : functor S P} (x : LFix S P) : App S P (LFix S P) :=
  match x with
  | LFix_in sh k => existT _ sh k
  end.

Lemma l_out_eq S P (F : functor S P) x y : x =e y -> l_out_f x  =e l_out_f y.
Proof. by case: x=> sx kx; case: y=> sy ky/= [/=Es Ek]; split. Qed.

Definition l_in S P (F : functor S P) : Alg S P (LFix S P) :=
  {| app := _; f_eq := @l_in_eq S P F |}.
Arguments l_in {S P F}.
Definition l_out S P (F : functor S P) : CoAlg S P (LFix S P) :=
  {| app := _; f_eq := @l_out_eq S P F |}.
Arguments l_out {S P F}.

Lemma l_in_out S P (F : functor S P) : l_in \o l_out =e id (A:=LFix S P).
Proof.
  move=>[s k]/=; split=>//= e d1 d2; rewrite (bool_irrelevance d1 d2).
  by apply: LFixR_refl.
Qed.

Lemma l_out_in  S P (F : functor S P)
  : l_out \o l_in =e id (A:=App S P (LFix S P)).
Proof.
  move=>[s k]/=; split=>//= e d1 d2; rewrite (bool_irrelevance d1 d2).
  by apply: LFixR_refl.
Qed.

Definition cata_f S P {F : functor S P} A {eA : equivalence A} (g : Alg S P A)
  : LFix S P -> A
  := fix f x :=
       match x with
       | LFix_in s k => g (existT _ s (comp f k))
       end.
Arguments cata_f {S P F A eA} g.

Lemma cata_arr S P {F : functor S P} A {eA : equivalence A} (g : Alg S P A)
  : forall x y, x =e y -> cata_f g x =e cata_f g y.
Proof.
  move=> x y /=; elim: x => sx kx Ih/= in y *; case: y=> sy ky/= [Es Ek].
  apply/(f_eq g); split=>//= e d1 d2; by apply/Ih.
Qed.

Definition cata S P {F : functor S P} A {eA : equivalence A} (g : Alg S P A)
  : LFix S P ~> A
  := {| app := _; f_eq := cata_arr g |}.
Arguments cata {S P F A eA} g.

Lemma cata_univ_r S P {F : functor S P} A {eA : equivalence A} (g : Alg S P A)
      (f : LFix S P ~> A)
  : f =e g \o fmap f \o l_out -> f =e cata g.
Proof.
  move=> H.
  elim=> sx kx /= Ih.
  rewrite (H _)/=; apply/f_eq; rewrite /fmap/=.
  split=>//= e d1 d2.
  rewrite Ih (cont_irr (X:=LFix S P) kx).
  by auto with ffix.
Qed.

Lemma cata_univ_l S P {F : functor S P} A {eA : equivalence A} (g : Alg S P A)
      (f : LFix S P ~> A)
  : f =e cata g -> f =e g \o fmap f \o l_out.
Proof.
  move=> H.
  elim=> sx kx /= Ih.
  rewrite (H _)/=; apply/(f_eq g); rewrite /fmap/=.
  split=>//= e d1 d2.
  rewrite Ih (cont_irr (X:=LFix S P) kx).
  rewrite -[cata_f g _]/(cata g _) -(H _) Ih.
  by auto with ffix.
Qed.

Lemma cata_univ S P {F : functor S P} A {eA : equivalence A} (g : Alg S P A)
      (f : LFix S P ~> A)
  : f =e cata g <-> f =e g \o fmap f \o l_out.
Proof. by split;[apply/cata_univ_l|apply/cata_univ_r]. Qed.

(* Finite anamorphisms *)
Inductive FinF S P {F : functor S P} A {eA : equivalence A}
          (h : CoAlg S P A) : A -> Prop :=
| FinF_fold x : (forall e, FinF h (projT2 (h x) e)) -> FinF h x.

Lemma FinF_inv S P {F : functor S P} A {eA : equivalence A} (h : CoAlg S P A) x
  : FinF h x -> forall e, FinF h (projT2 (h x) e).
Proof. by case. Defined.

(* Finite coalgebras *)
Definition FCoAlg S P {F : functor S P} A {eA : equivalence A} :=
  sig (fun f => forall x, FinF f x).
Arguments FCoAlg S P {F} A {eA}.

Coercion coalg S P {F : functor S P} A {eA : equivalence A}
  : FCoAlg S P A -> A ~> App S P A := sval.

Definition finite S P {F : functor S P} A {eA : equivalence A}
  : forall (h : FCoAlg S P A) x, FinF h x := @proj2_sig _ _.

Definition ana_f_ S P {F : functor S P} A {eA : equivalence A} (h : CoAlg S P A)
  : forall (x : A), FinF h x -> LFix S P
  := fix f x H :=
       let hx := h x in
       LFix_in (fun e => f (projT2 hx e) (FinF_inv H e)).

Lemma ana_f_irr S P {F : functor S P} A {eA : equivalence A} (h : CoAlg S P A)
  : forall (x : A) (F1 F2 : FinF h x), ana_f_ F1 =e ana_f_ F2.
Proof.
  move=>/=; fix Ih 2; move=> x [{}x Fx] F2; move: F2 Fx=> [{}x Fy] Fx/=.
  split=>// e d1 d2; rewrite (bool_irrelevance d2 d1) => {d2}.
  by apply: Ih.
Qed.

Definition ana_f S P {F : functor S P} A {eA : equivalence A} (h : FCoAlg S P A)
  : A -> LFix S P
  := fun x => ana_f_ (finite h x).

Lemma ana_arr S P {F : functor S P} A {eA : equivalence A} (h : FCoAlg S P A)
  : forall x y, x =e y -> ana_f h x =e ana_f h y.
Proof.
  rewrite /ana_f; move=> x y; move: x y (finite h x) (finite h y).
  fix Ih 3; move=> x y [x' Fx] [y' Fy]/=; split.
  - by case: (f_eq h H).
  - move=> e d1 d2 /=; apply: Ih.
    by move: (f_eq h H)=> [E1 /(_ e d1 d2)].
Qed.

Definition ana S P (F : functor S P) A (eA : equivalence A)
           (h : FCoAlg S P A) : A ~> LFix S P
  := {| app := ana_f h; f_eq := ana_arr h |}.

Lemma ana_univ_r S P (F : functor S P) A (eA : equivalence A)
      (h : FCoAlg S P A) (f : A ~> LFix S P)
  : f =e l_in \o fmap f \o h -> f =e ana h.
Proof.
  move=> H; rewrite /ana/ana_f/==>x; move: x (finite h x).
  fix Ih 2; move=> x [{}x Fx].
  rewrite -[LFixR (f x) _]/(@eqRel _ LFix_Eq (f x) _) (H _)/=; split=>// e d1 d2.
  rewrite (bool_irrelevance d2 d1); by apply: Ih.
Qed.

Lemma ana_univ_l S P {F : functor S P} A {eA : equivalence A}
      (h : FCoAlg S P A) (f : A ~> LFix S P)
  : f =e ana h -> f =e l_in \o fmap f \o h.
Proof.
  move=> H x; move: x (finite h x).
  fix Ih 2; move=> x [{}x Fx].
  rewrite (H _) /=/ana_f; move: (finite h x)=>Fx'; move: Fx' Fx.
  move=>[{}x Fx'] Fx/=; split=>// e d1 d2.
  rewrite (bool_irrelevance d2 d1).
  rewrite -[LFixR _ _]/(@eqRel _ LFix_Eq _ _).
  move: (H (projT2 (coalg h x) (exist _ e d1))); rewrite /ana/ana_f/=.
  rewrite -![LFixR _ _]/(@eqRel _ LFix_Eq _ _).
  rewrite ana_f_irr =><-/=; by apply: LFixR_refl.
Qed.

Lemma ana_univ S P {F : functor S P} A {eA : equivalence A}
      (h : FCoAlg S P A) (f : A ~> LFix S P)
  : f =e ana h <-> f =e l_in \o fmap f \o h.
Proof. by split;[apply/ana_univ_l|apply/ana_univ_r]. Qed.

(** Hylomorphisms **)

Print FinF_inv.

Definition hylo_f_ S P {F : functor S P}
           A B {eA : equivalence A} {eB : equivalence B}
           (g : Alg S P B) (h : CoAlg S P A)
  : forall (x : A), FinF h x -> B
  := fix f x H :=
       match h x as h0
             return
             (forall e : {x0 : P | dom (projT1 h0) x0}, FinF h (projT2 h0 e)) ->
             B
       with
       | existT s_x c_x => fun H => g (existT _ s_x (fun e => f (c_x e) (H e)))
       end (FinF_inv H).

Lemma hylo_f_irr S P {F : functor S P}
           A B {eA : equivalence A} {eB : equivalence B}
           (g : Alg S P B) (h : CoAlg S P A)
  : forall (x : A) (F1 F2 : FinF h x), hylo_f_ g F1 =e hylo_f_ g F2.
Proof.
  move=>/=; fix Ih 2; move=> x [{}x Fx] F2; move: F2 Fx=> [{}x Fy] Fx/=.
  move: (h x) Fx Fy => [s_x c_x]/= Fx Fy.
  apply/f_eq=>/=; split=>//= e d1 d2; rewrite (bool_irrelevance d2 d1)=>{d2}.
  by apply: Ih.
Qed.

Definition hylo_f S P {F : functor S P}
           A B {eA : equivalence A} {eB : equivalence B}
           (g : Alg S P B) (h : FCoAlg S P A)
  := fun x => hylo_f_ g (finite h x).

Lemma hylo_arr S P {F : functor S P}
           A B {eA : equivalence A} {eB : equivalence B}
           (g : Alg S P B) (h : FCoAlg S P A)
  : forall x y, x =e y -> hylo_f g h x =e hylo_f g h y.
Proof.
  rewrite /hylo_f; move=> x y; move: x y (finite h x) (finite h y).
  fix Ih 3; move=> x y [x' Fx] [y' Fy]/= H.
  move: (@f_eq _ _ _ _ h _ _ H).
  move: (h x') (h y') Fx Fy => [s_x c_x] [s_y c_y]/= Fx Fy [/=Es Ec].
  apply/f_eq=>/=; split=>//= e d1 d2.
  by apply/Ih/Ec.
Qed.

Definition hylo S P {F : functor S P}
           A B {eA : equivalence A} {eB : equivalence B}
           (g : Alg S P B) (h : FCoAlg S P A)
  : A ~> B
  := {| app := _ ; f_eq := hylo_arr g h |}.

Lemma hylo_univ_r S P {F : functor S P}
      A B {eA : equivalence A} {eB : equivalence B}
      (g : Alg S P B) (h : FCoAlg S P A) (f : A ~> B)
  : f =e g \o fmap f \o h -> f =e hylo g h.
Proof.
  move=> H; rewrite /hylo/hylo_f/==>x; move: x (finite h x).
  fix Ih 2; move=> x Fx; rewrite (H _)/=/fmap/=; case: Fx=> {}x Fx/=.
  move: (h x) Fx => [s_x c_x]/= Fx.
  apply/f_eq => /=; split=>//= e d1 d2.
  by rewrite (bool_irrelevance d2 d1); apply/Ih.
Qed.

Lemma hylo_univ_l S P {F : functor S P}
      A B {eA : equivalence A} {eB : equivalence B}
      (g : Alg S P B) (h : FCoAlg S P A) (f : A ~> B)
  : f =e hylo g h -> f =e g \o fmap f \o h.
Proof.
  move=> H x; move: x (finite h x).
  fix Ih 2; move=> x [{}x Fx].
  rewrite (H _) /=/hylo_f; move: (finite h x)=>Fx'; move: Fx' Fx.
  move=>[{}x Fx']/=; case: (h x) Fx' => /=s_x c_x Fx' Fx.
  apply/f_eq; split=>//= e d1 d2.
  rewrite (bool_irrelevance d2 d1) (H _) /=/hylo_f/= hylo_f_irr.
  by eauto with ffix.
Qed.

Lemma hylo_univ S P {F : functor S P}
      A B {eA : equivalence A} {eB : equivalence B}
      (g : Alg S P B) (h : FCoAlg S P A) (f : A ~> B)
  : f =e hylo g h <-> f =e g \o fmap f \o h.
Proof. by split;[apply/hylo_univ_l|apply/hylo_univ_r]. Qed.

Corollary hylo_unr S P {F : functor S P}
      A B {eA : equivalence A} {eB : equivalence B}
      (g : Alg S P B) (h : FCoAlg S P A)
  : hylo g h =e g \o fmap (hylo g h) \o h.
Proof. by rewrite -hylo_univ; reflexivity. Qed.

Lemma fin_out S P (F : functor S P) : forall x, FinF l_out x.
Proof. by elim=>s k Ih; constructor; apply: Ih. Qed.

Definition f_out S P (F : functor S P) : FCoAlg S P (LFix S P) :=
  exist _ _ (@fin_out S P F).
Arguments f_out {S P F}.

Lemma hylo_cata S P {F : functor S P} B {eB : equivalence B} (g : Alg S P B)
  : cata g =e hylo g f_out.
Proof. rewrite hylo_univ; apply/cata_univ; reflexivity. Qed.

Lemma hylo_ana  S P {F : functor S P} A {eA : equivalence A} (h : FCoAlg S P A)
  : ana h =e hylo l_in h.
Proof. by rewrite hylo_univ; apply/ana_univ; reflexivity. Qed.

Lemma compA A B C D {eA : equivalence A} {eB : equivalence B}
      {eC : equivalence C} {eD : equivalence D}
      (f : C ~> D) (g : B ~> C) (h : A ~> B)
  : f \o (g \o h) =e (f \o g) \o h.
Proof. move=>x; by eauto with ffix. Qed.

Lemma idKl A B {eA : equivalence A} {eB : equivalence B} (f : A ~> B)
  : f \o id =e f.
Proof. move=> x; by eauto with ffix. Qed.

Lemma idKr A B {eA : equivalence A} {eB : equivalence B} (f : A ~> B)
  : id \o f =e f.
Proof. move=> x; by eauto with ffix. Qed.

Lemma splitC A B C
      {eA : equivalence A} {eB : equivalence B} {eC : equivalence C}
      (f1 f2 : B ~> C) (g1 g2 : A ~> B)
  : f1 =e f2 -> g1 =e g2 -> f1 \o g1 =e f2 \o g2.
Proof. by move=>->->; eauto with ffix. Qed.

Lemma hylo_fusion_l S P {F : functor S P} A B C
      {eA : equivalence A} {eB : equivalence B} {eC : equivalence C}
      (h1 : FCoAlg S P A) (g1 : Alg S P B) (g2 : Alg S P C) (f2 : B ~> C)
      (E2 : f2 \o g1 =e g2 \o fmap f2)
  : f2 \o hylo g1 h1 =e hylo g2 h1.
Proof.
  rewrite hylo_univ fmap_comp.
  rewrite compA -E2 -compA -compA.
  apply/splitC; first by reflexivity.
  rewrite compA -hylo_univ.
  reflexivity.
Qed.

Lemma hylo_fusion_r S P {F : functor S P} A B C
      {eA : equivalence A} {eB : equivalence B} {eC : equivalence C}
      (h1 : FCoAlg S P B) (g1 : Alg S P C) (h2 : FCoAlg S P A)
      (f1 : A ~> B) (E1 : h1 \o f1 =e fmap f1 \o h2)
  : hylo g1 h1 \o f1 =e hylo g1 h2.
Proof.
  rewrite hylo_univ fmap_comp.
  rewrite -!compA -E1 !compA.
  apply/splitC; last by reflexivity.
  rewrite -hylo_univ.
  reflexivity.
Qed.

Lemma deforest S P {F : functor S P} A B C
      {eA : equivalence A} {eB : equivalence B} {eC : equivalence C}
      (h1 : FCoAlg S P A) (g1 : Alg S P B) (h2 : FCoAlg S P B) (g2 : Alg S P C)
      (INV: h2 \o g1 =e id)
  : hylo g2 h2 \o hylo g1 h1 =e hylo g2 h1.
Proof.
  apply/hylo_fusion_l.
  rewrite [in H in H =e _]hylo_unr.
  rewrite -compA INV idKl.
  reflexivity.
  Restart.
  apply/hylo_fusion_r.
  rewrite [in H in H =e _]hylo_unr.
  rewrite compA compA INV idKr.
  reflexivity.
Qed.

Corollary cata_ana_hylo S P (F : functor S P)
          A B {eA : equivalence A} {eB : equivalence B}
          (g : Alg S P B) (h : FCoAlg S P A)
  : cata g \o ana h =e hylo g h.
Proof. by rewrite hylo_cata hylo_ana; apply/deforest/l_out_in. Qed.

Section ExQsort.

  (* Defining a tree *)
  Inductive Ts A := | Leaf | Node (ELEM : A). (* shapes *)
  Inductive Tp := | Lbranch | Rbranch. (* positions *)
  Definition t_dom A (s : Ts A) : Tp -> bool := (* position valid in shape? *)
    match s with
    | Node _ => fun=>true
    | _ => fun=> false
    end.
  Instance tree_func A : functor (Ts A) Tp :=
    { dom := @t_dom  A
    }.

  Lemma dom_leaf_false A : {y | t_dom (Leaf A) y} -> False.
  Proof. by move=>[]. Qed.
  Definition dom_leaf A B (x : {y | t_dom (Leaf A) y}) : B :=
    False_rect _ (dom_leaf_false x).

  Definition a_leaf A X : App (Ts A) Tp X := existT _ (Leaf A) (@dom_leaf A _).
  Definition a_node A X (x : A) (l r : X) : App (Ts A) Tp X :=
    existT _ (Node x) (fun p => match proj1_sig p with
                                | Lbranch => l
                                | Rbranch => r
                                end).

  Definition a_out A X (x : App (Ts A) Tp X)
    : option (A * X * X)
    := match x with
       | existT s k =>
         match s return (sig (t_dom s) -> X) -> _ with
         | Leaf => fun=> None
         | Node x =>
           fun k=>
             Some (x,
                   k (exist _ Lbranch is_true_true),
                   k (exist _ Rbranch is_true_true))
         end k
       end.
  (* end tree *)

  Instance eq_seq_nat : equivalence (seq nat) :=
    { eqRel := eq;
      e_refl := @erefl (seq nat);
      e_sym := @esym (seq nat);
      e_trans := @etrans (seq nat);
    }.

  Definition m_merge (x : App (Ts nat) Tp (seq nat)) : seq nat :=
    match a_out x with
    | None => [::]
    | Some (h, l, r) => l ++ h :: r
    end.
    (* match projT1 x as sh return (sig (dom sh) -> seq nat) -> seq nat with *)
    (* | Leaf => fun=>[::] *)
    (* | Node h => fun k=> k (exist _ Lbranch is_true_true) ++ h :: k (exist _ Rbranch is_true_true) *)
    (* end (projT2 x). *)
  Lemma m_merge_arr : forall x y, x =e y -> m_merge x =e m_merge y.
  Proof.
    move=>[[|hx]/= kx]/= [[|hy]//= ky] [//= [<-]] H.
    by rewrite /m_merge/= !H.
  Qed.
  Definition merge : Alg (Ts nat) Tp (seq nat)
    := {| app := m_merge; f_eq := m_merge_arr |}.

  Definition m_split (x : seq nat) : App (Ts nat) Tp (seq nat) :=
    match x with
    | [::] => a_leaf _ _
    | h :: t => a_node h [seq x <- t | x <= h] [seq x <- t | x > h]
    end.
  Lemma m_split_arr : forall x y, x =e y -> m_split x =e m_split y.
  Proof. by move=> x y ->; eauto with ffix. Qed.
  Definition c_split : CoAlg (Ts nat) Tp (seq nat)
    := {| app := m_split; f_eq := m_split_arr |}.

  (* Needs to be defined, otherwise msort does not reduce! *)
  Lemma split_fin : forall x, FinF c_split x.
  Proof.
    move=>x; move: {-1}(size x) (leqnn (size x))=> n.
    elim: n => [|n Ih] in x *; case: x=> [|h t]/=; eauto=>E; constructor=>/=.
    - by case.
    - by [].
    - move=> [e /=_]; apply/Ih.
      by case: e; rewrite size_filter (leq_trans (count_size _ _)).
  Defined.

  Definition tsplit : FCoAlg (Ts nat) Tp (seq nat)
    := exist _ c_split split_fin.
  Definition msort : seq nat -> seq nat := hylo merge tsplit.
End ExQsort.

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
(* Set Extraction TypeExpand. *)
Extraction Inline app.
Extraction Inline coalg.
Extraction Inline hylo.
Extraction Inline hylo_f.
Extraction Inline hylo_f_.
Extraction Inline projT1.
Extraction Inline projT2.

Extraction Inline merge.
Extraction Inline a_leaf.
Extraction Inline a_node.
Extraction Inline m_merge.
Extraction Inline m_split.
Extraction Inline a_out.
Extraction Inline c_split.
Extraction Inline tsplit.
Set Extraction Flag 2047.
Extraction "test.ml" Ts Tp dom_leaf leq filter msort.
