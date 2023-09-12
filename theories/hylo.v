(* From mathcomp Require Import all_ssreflect. *)
Require Import Coq.Logic.Eqdep_dec.
Require Import Setoid.


Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Unset Auto Template Polymorphism.


Module BoolEq <: DecidableType.
  Definition U := bool.
  Lemma eq_dec (b1 b2 : U) : {b1 = b2} + {b1 <> b2}.
  Proof.
    decide equality.
  Qed.
End BoolEq.
Module DecBool := DecidableEqDep(BoolEq).

Definition bool_irrelevance {b1 b2 : bool} (p1 p2 : b1 = b2) : p1 = p2 :=
  DecBool.UIP b1 b2 p1 p2.

(****************************************************************************)
(** Assumptions and Strict positivisation of functors                      **)
(****************************************************************************)
Class equiv A : Type :=
  MkEquiv
    { eqRel : A -> A -> Prop;
      e_refl : forall x, eqRel x x;
      e_sym : forall x y, eqRel x y -> eqRel y x;
      e_trans : forall x y z, eqRel x y -> eqRel y z -> eqRel x z;
    }.

#[export] Hint Resolve e_refl : ffix.
#[export] Hint Resolve e_sym : ffix.
#[export] Hint Resolve e_trans : ffix.

#[export] Instance def_eq A : equiv A | 100 :=
  {| eqRel := @eq A;
     e_refl := @eq_refl A;
     e_sym := @eq_sym A;
     e_trans := @eq_trans A;
  |}.

Add Parametric Relation `{eq : equiv A} : A (@eqRel A eq)
    reflexivity proved by (@e_refl A eq)
    symmetry proved by (@e_sym A eq)
    transitivity proved by (@e_trans A eq)
      as ExtEq.

Reserved Notation "f =e g" (at level 70, no associativity).
Notation "f =e g" := (eqRel f g).

#[export] Instance ext_eq (A : Type) `{eq_B : equiv B} : equiv (A -> B).
Proof with eauto with ffix.
  apply (@MkEquiv _ (fun f g =>forall x, eqRel (f x) (g x)))...
Defined.

(** Is position valid in shape? *)
Class functor (S P : Type) :=
  { dom : S -> P -> bool
  }.

Definition elem_of `{F : functor Sh P} (s : Sh) := {x | dom s x = true}.
Definition App `{F : functor Sh P} (X : Type) := {sh & elem_of sh -> X}.
Arguments App Sh P {F} X.

Lemma cont_irr `{F : functor Sh P} X sh (f : elem_of sh -> X)
  : forall x p1 p2, f (exist _ x p1) = f (exist _ x p2).
Proof.
  simpl; intros x p1 p2.
  rewrite (bool_irrelevance p1 p2).
  reflexivity.
Qed.

Definition AppR `{F : functor Sh P} (X : Type) {e : equiv X}
           (x y : App Sh P X) : Prop
  := projT1 x = projT1 y /\
     (forall e d1 d2, projT2 x (exist _ e d1) =e projT2 y (exist _ e d2)).

Lemma AppR_inv_sh `{F : functor Sh P} X {e : equiv X} x y :
  AppR x y -> projT1 x = projT1 y.
Proof. intros []. trivial. Qed.

Lemma AppR_inv_k `{F : functor Sh P} `{e : equiv X} x y :
  AppR x y ->
  forall e d1 d2, projT2 x (exist _ e d1) =e projT2 y (exist _ e d2).
Proof. intros []. trivial. Qed.

#[export] Instance App_equiv `{F : functor Sh P} `{e : equiv X}
  : equiv (App Sh P X).
Proof with eauto with ffix.
  apply (@MkEquiv _ (@AppR Sh P F X e)).
  - intros [shx kx]. constructor...
    simpl. intros x d1 d2.
    rewrite (bool_irrelevance d1 d2).
    reflexivity.
  - intros x y [Sxy Exy].
    split...
  - intros x y z [Sxy Exy] [Syz Eyz]; simpl; split.
    * rewrite Sxy...
    * intros t d1 d2.
      assert (dom (projT1 y) t = true) as d3 by (rewrite <-Sxy; trivial).
      rewrite (Exy t d1 d3)...
Defined.

Structure morph `{eq_A : equiv A} `{eq_B : equiv B}
  := { app :> A -> B;
       f_eq : forall x y, x =e y -> app x =e app y
     }.
Arguments morph A {eq_A} B {eq_B}.

Reserved Notation "x ~> y" (at level 95, right associativity, y at level 200).
Notation "x ~> y" := (morph x y).

#[export] Instance eq_morph `{eq_A : equiv A} `{eq_B : equiv B}
  : equiv (A ~> B).
Proof with eauto with ffix.
  apply (@MkEquiv _ (fun f g =>forall x, app f x =e app g x))...
Defined.

(* Definition arr (A B : Type) (eq_A : equiv A) (eq_B : equiv B) *)
(*   := sig (@morph A B eq_A eq_B). *)

Reserved Notation "f \o g" (at level 50, format "f  \o '/ '  g").
Local Definition comp A B C (f : B -> C) (g : A -> B) x := f (g x).
Notation "f \o g" := (comp f g).

Definition fmapA `{F : functor Sh P} `(f : A -> B) (x : App Sh P A)
  : App Sh P B
  := existT _ (projT1 x) (f \o projT2 x).

Lemma fmapA_eqF `{F : functor Sh P} `{eA : equiv A} `{eB : equiv B}
      (f : A ~> B)
  : forall x y, x =e y -> fmapA f x =e fmapA f y.
Proof with eauto with ffix.
  intros [sx kx] [sy ky] [Es Ek]. split; auto. intros.  apply f_eq. auto.
Qed.

Definition fmap `{F : functor Sh P} `{eA : equiv A} `{eB : equiv B}
  (f : A ~> B) : App Sh P A ~> App Sh P B
  := {| app := _ ; f_eq := fmapA_eqF f |}.

Lemma comp_eq `{e1 : equiv A} `{e2 : equiv B} `{e3 : equiv C}
      (f : B ~> C) (g : A ~> B) :
  forall x y, x =e y -> (f \o g) x =e (f \o g) y.
Proof. intros. do 2 apply f_eq. trivial. Qed.

Definition acomp `{e1 : equiv A} `{e2 : equiv B} `{e3 : equiv C}
      (f : B ~> C) (g : A ~> B) : A ~> C
  := {| app := _; f_eq := comp_eq f g |}.

Notation "f \o g" := (acomp f g).

Lemma id_eq `{eq_A : equiv A} : forall (x y : A), x =e y -> id x =e id y.
Proof. trivial. Qed.

Definition id `{eq : equiv A} : A ~> A :=
  {| app := _; f_eq := @id_eq A eq |}.
Arguments id {A eq}.

Lemma fmap_id `{F : functor Sh P} `{eq_A : equiv A} : fmap id =e id.
Proof.
  intros [s k]. unfold fmap. simpl.
  split; try trivial.
  intros e d1 d2.
  rewrite (bool_irrelevance d2 d1).
  reflexivity.
Qed.

Lemma fmap_comp `{F : functor Sh P} `{eq_A : equiv A} `{eq_B : equiv B}
      `{eq_C :equiv C} (f : B ~> C) (g : A ~> B)
  : fmap (f \o g) =e fmap f \o fmap g.
Proof.
  intros [s k]. unfold fmap. simpl.
  split; try trivial.
  intros e d1 d2.
  rewrite (bool_irrelevance d2 d1).
  reflexivity.
Qed.

Add Parametric Morphism `(F : functor Sh P) `{e1 : equiv A} `{e2 : equiv B}
  : (@fmap Sh P F A e1 B e2)
    with signature
    (eqRel (A:=A ~> B))
      ==> (eqRel (A:=App Sh P A ~> App Sh P B))
      as fmapMorphism.
Proof.
  intros f1 f2 Ef [s k].
  split; try trivial.
  simpl.
  intros e d1 d2.
  unfold comp.
  rewrite (bool_irrelevance d1 d2).
  apply Ef.
Qed.

Add Parametric Morphism `{eA : equiv A} `{eB : equiv B} `{eC : equiv C}
  : (@acomp A eA B eB C eC)
    with signature
    (eqRel (A:=B ~> C))
      ==> (eqRel (A:=A ~> B))
      ==> (eqRel (A:=A ~> C))
      as compMorphism.
Proof.
  intros f1 f2 Ef g1 g2 Eg x.
  apply (e_trans (Ef (g1 x))).
  simpl. unfold comp.
  apply f_eq.
  apply Eg.
Qed.

Definition Alg S P {F : functor S P} A {eA : equiv A} := App S P A ~> A.
Arguments Alg S P {F} A {eA}.
Definition CoAlg S P {F : functor S P} A {eA : equiv A} := A ~> App S P A.
Arguments CoAlg S P {F} A {eA}.

Inductive LFix S P {F : functor S P} : Type :=
| LFix_in sh : (elem_of sh -> @LFix S P F) -> @LFix S P F.
Arguments LFix S P {F}.

Definition l_shape S P {F : functor S P} (x : LFix S P) :=
  match x with
  | @LFix_in _ _ _ sh _ => sh
  end.
Definition l_cont S P {F : functor S P} (x : LFix S P) :=
  match x return elem_of (l_shape x) -> LFix S P with
  | LFix_in k => k
  end.

Fixpoint LFixR S P {F : functor S P} (x y : LFix S P) : Prop :=
  l_shape x = l_shape y /\
  forall e d1 d2,
      LFixR (l_cont (x:=x) (exist _ e d1)) (l_cont (x:=y) (exist _ e d2)).

Lemma LFixR_inv_sh S P {F : functor S P} (x y : LFix S P)
  : LFixR x y -> l_shape x = l_shape y.
Proof. destruct x,y. intros []. auto. Qed.

Lemma LFixR_inv_k S P {F : functor S P} (x y : LFix S P)
  : LFixR x y ->
    forall e d1 d2,
      LFixR (l_cont (x:=x) (exist _ e d1)) (l_cont (x:=y) (exist _ e d2)).
Proof. destruct x,y. intros []. auto. Qed.

Lemma LFixR_refl S P {F : functor S P} (x : LFix S P) : LFixR x x.
Proof.
  induction x as [shk k Ik].
  split; simpl; try trivial.
  intros x p1 p2.
  rewrite (bool_irrelevance p1 p2).
  trivial.
Qed.

Lemma LFixR_sym S P {F : functor S P} (x y : LFix S P) : LFixR x y -> LFixR y x.
Proof.
  revert y.
  induction x as [sx kx Ih].
  intros [sy ky] [Sxy H].
  split; auto.
Qed.

Lemma LFixR_trans S P {F : functor S P} (x y z : LFix S P)
  : LFixR x y -> LFixR y z -> LFixR x z.
Proof.
  revert y z.
  induction x as [sx kx Ih].
  intros y z.
  destruct y as [sy ky]; simpl.
  destruct z as [sz kz]; simpl.
  intros [Sxy Exy] [Syz Eyz].
  split; [rewrite Sxy; trivial | idtac].
  intros e d1 d2.
  assert (dom sy e = true) as d by (rewrite Syz; trivial).
  apply (Ih _ _ _ (Exy _ _ d)).
  trivial.
Qed.

#[export] Instance LFix_Eq S P {F : functor S P} : equiv (LFix S P) :=
  {| eqRel := @LFixR S P F;
     e_refl := @LFixR_refl S P F;
     e_sym := @LFixR_sym S P F;
     e_trans := @LFixR_trans S P F;
  |}.

Definition l_in_f S P {F : functor S P} (x : App S P (LFix S P)) : LFix S P :=
  LFix_in (projT2 x).

Lemma l_in_eq S P {F : functor S P} x y : x =e y -> l_in_f x =e l_in_f y.
Proof. destruct x, y; auto. Qed.

Definition l_out_f S P {F : functor S P} (x : LFix S P) : App S P (LFix S P) :=
  match x with
  | LFix_in k => existT _ _ k
  end.

Lemma l_out_eq S P (F : functor S P) x y : x =e y -> l_out_f x  =e l_out_f y.
Proof. destruct x,y; auto. Qed.

Definition l_in S P (F : functor S P) : Alg S P (LFix S P) :=
  {| app := _; f_eq := @l_in_eq S P F |}.
Arguments l_in {S P F}.
Definition l_out S P (F : functor S P) : CoAlg S P (LFix S P) :=
  {| app := _; f_eq := @l_out_eq S P F |}.
Arguments l_out {S P F}.

Lemma l_in_out S P (F : functor S P) : l_in \o l_out =e id (A:=LFix S P).
Proof.
  intros []; split; [reflexivity | simpl; intros e d1 d2].
  rewrite (bool_irrelevance d1 d2).
  apply LFixR_refl.
Qed.

Lemma l_out_in  S P (F : functor S P)
  : l_out \o l_in =e id (A:=App S P (LFix S P)).
Proof.
  intros []; split; [reflexivity | simpl; intros e d1 d2].
  rewrite (bool_irrelevance d1 d2).
  apply LFixR_refl.
Qed.

Definition cata_f S P {F : functor S P} A {eA : equiv A} (g : Alg S P A)
  : LFix S P -> A
  := fix f x :=
       match x with
       | LFix_in k => g (existT _ _ (comp f k))
       end.
Arguments cata_f {S P F A eA} g.

Lemma cata_arr S P {F : functor S P} A {eA : equiv A} (g : Alg S P A)
  : forall x y, x =e y -> cata_f g x =e cata_f g y.
Proof.
  induction x as [sx kx Ih]. destruct y as [sy ky]. simpl in *. intros [Es Ek].
  apply (f_eq g). split; [trivial|intros e d1 d2]. apply Ih. auto.
Qed.

Definition cata S P {F : functor S P} A {eA : equiv A} (g : Alg S P A)
  : LFix S P ~> A
  := {| app := _; f_eq := cata_arr g |}.
Arguments cata {S P F A eA} g.

Lemma cata_univ_r S P {F : functor S P} A {eA : equiv A} (g : Alg S P A)
      (f : LFix S P ~> A)
  : f =e g \o fmap f \o l_out -> f =e cata g.
Proof.
  intros H e. induction e as [sx kx Ih]. simpl in *. rewrite H. apply f_eq.
  split; [trivial|intros e d1 d2]. simpl. unfold comp at 1. rewrite Ih.
  rewrite (bool_irrelevance d1 d2). auto with ffix.
Qed.

Lemma cata_univ_l S P {F : functor S P} A {eA : equiv A} (g : Alg S P A)
      (f : LFix S P ~> A)
  : f =e cata g -> f =e g \o fmap f \o l_out.
Proof.
  intros H e. case e as [sx kx]. simpl in *. rewrite H. apply f_eq. simpl.
  split; [trivial|intros e d1 d2]. simpl. fold (cata_f g). unfold comp at 1.
  rewrite <- H. rewrite (bool_irrelevance d2 d1). auto with ffix.
Qed.

Lemma cata_univ S P {F : functor S P} A {eA : equiv A} (g : Alg S P A)
      (f : LFix S P ~> A)
  : f =e cata g <-> f =e g \o fmap f \o l_out.
Proof. split;[apply cata_univ_l|apply cata_univ_r]. Qed.

(* Finite anamorphisms *)
Inductive FinF S P {F : functor S P} A {eA : equiv A}
          (h : CoAlg S P A) : A -> Prop :=
| FinF_fold x : (forall e, FinF h (projT2 (h x) e)) -> FinF h x.
#[export] Hint Constructors FinF : ffix.

Lemma FinF_inv S P {F : functor S P} A {eA : equiv A} (h : CoAlg S P A) x
  : FinF h x -> forall e, FinF h (projT2 (h x) e).
Proof. intros []. auto. Defined.

(* Finite coalgebras *)
Definition FCoAlg S P {F : functor S P} A {eA : equiv A} :=
  sig (fun f => forall x, FinF f x).
Arguments FCoAlg S P {F} A {eA}.

Coercion coalg S P {F : functor S P} A {eA : equiv A}
  : FCoAlg S P A -> A ~> App S P A := @proj1_sig _ _.

Definition finite S P {F : functor S P} A {eA : equiv A}
  : forall (h : FCoAlg S P A) x, FinF h x := @proj2_sig _ _.

Definition ana_f_ S P {F : functor S P} A {eA : equiv A} (h : CoAlg S P A)
  : forall (x : A), FinF h x -> LFix S P
  := fix f x H :=
       let hx := h x in
       LFix_in (fun e => f (projT2 hx e) (FinF_inv H e)).

Lemma ana_f_irr S P {F : functor S P} A {eA : equiv A} (h : CoAlg S P A)
  : forall (x : A) (F1 F2 : FinF h x), ana_f_ F1 =e ana_f_ F2.
Proof.
  simpl. fix Ih 2. intros x0 [x Fx] F2. clear x0. destruct F2 as [x Fy].
  simpl. split; [trivial| intros e d1 d2]. rewrite (bool_irrelevance d2 d1).
  apply Ih. Guarded.
Qed.

Definition ana_f S P {F : functor S P} A {eA : equiv A} (h : FCoAlg S P A)
  : A -> LFix S P
  := fun x => ana_f_ (finite h x).

Lemma ana_arr S P {F : functor S P} A {eA : equiv A} (h : FCoAlg S P A)
  : forall x y, x =e y -> ana_f h x =e ana_f h y.
Proof.
  unfold ana_f. intros x y. generalize (finite h x) (finite h y). revert x y.
  fix Ih 3. intros x y [x' Fx] [y' Fy] Hxy. simpl. split.
  - destruct (f_eq h Hxy). auto.
  - intros e d1 d2. simpl. apply Ih. Guarded.
    destruct (f_eq h Hxy). auto.
Qed.

Lemma LFixR_fold `{F : functor Sh P} (x y : LFix Sh P) : LFixR x y = (x =e y).
Proof. auto. Qed.

Definition ana S P (F : functor S P) A (eA : equiv A)
           (h : FCoAlg S P A) : A ~> LFix S P
  := {| app := ana_f h; f_eq := ana_arr h |}.

Lemma ana_univ_r S P (F : functor S P) A (eA : equiv A)
      (h : FCoAlg S P A) (f : A ~> LFix S P)
  : f =e l_in \o fmap f \o h -> f =e ana h.
Proof.
  intros H. unfold ana, ana_f. simpl. intros x. generalize (finite h x).
  revert x.  fix Ih 2. intros x0 [x Fx]. clear x0.
  rewrite LFixR_fold, (H _). simpl.
  split; [trivial| intros e d1 d2]. rewrite (bool_irrelevance d2 d1). apply Ih.
Qed.

Lemma ana_univ_l S P {F : functor S P} A {eA : equiv A}
      (h : FCoAlg S P A) (f : A ~> LFix S P)
  : f =e ana h -> f =e l_in \o fmap f \o h.
Proof.
  intros H x0. rewrite (H _). simpl. unfold ana_f.
  generalize (finite h x0) as Fx. intros [x Fx]. clear x0. simpl.
  split; [trivial | intros e d1 d2]. rewrite (bool_irrelevance d2 d1).
  generalize (H (projT2 (coalg h x) (exist _ e d1))). unfold ana, ana_f. simpl.
  unfold comp. rewrite !LFixR_fold. intros Hrw. rewrite Hrw. apply ana_f_irr.
Qed.

Lemma ana_univ S P {F : functor S P} A {eA : equiv A}
      (h : FCoAlg S P A) (f : A ~> LFix S P)
  : f =e ana h <-> f =e l_in \o fmap f \o h.
Proof. split;[apply ana_univ_l|apply ana_univ_r]. Qed.

(** Hylomorphisms **)

Definition hylo_f_ S P {F : functor S P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg S P B) (h : CoAlg S P A)
  : forall (x : A), FinF h x -> B
  := fix f x H :=
       match h x as h0
             return
             (forall e : elem_of (projT1 h0), FinF h (projT2 h0 e)) ->
             B
       with
       | existT _ s_x c_x => fun H => g (existT _ s_x (fun e => f (c_x e) (H e)))
       end (FinF_inv H).

Lemma hylo_f_irr S P {F : functor S P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg S P B) (h : CoAlg S P A)
  : forall (x : A) (F1 F2 : FinF h x), hylo_f_ g F1 =e hylo_f_ g F2.
Proof.
  fix Ih 2. intros x0 [x Fx] F2. clear x0. destruct F2 as [x Fy]. simpl.
  generalize dependent (h x).  clear x. intros [s_x c_x] Fx Fy. simpl in *.
  apply f_eq. split; [trivial|intros e d1 d2]. rewrite (bool_irrelevance d2 d1).
  simpl in *. apply Ih. Guarded.
Qed.

Definition hylo_f S P {F : functor S P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg S P B) (h : FCoAlg S P A)
  := fun x => hylo_f_ g (finite h x).

Lemma hylo_arr S P {F : functor S P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg S P B) (h : FCoAlg S P A)
  : forall x y, x =e y -> hylo_f g h x =e hylo_f g h y.
Proof.
  unfold hylo_f.
  intros x y. generalize x,y,(finite h x),(finite h y). clear x y.
  fix Ih 3. intros x y [x' Fx] [y' Fy] H. simpl.
  generalize (@f_eq _ _ _ _ h _ _ H). revert Fx Fy.
  generalize (h x') (h y'). intros [s_x c_x] [s_y c_y]. simpl.
  intros Fx Fy [Exy Ec]. simpl in *.
  apply f_eq. split; [trivial|simpl; intros e d1 d2].
  apply Ih. Guarded. apply Ec.
Qed.

Definition hylo S P {F : functor S P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg S P B) (h : FCoAlg S P A)
  : A ~> B
  := {| app := _ ; f_eq := hylo_arr g h |}.

(* "universal" (quotes) because these are *finite* hylos, otherwise this
   direction would not work
 *)
Lemma hylo_univ_r S P {F : functor S P}
      A B {eA : equiv A} {eB : equiv B}
      (g : Alg S P B) (h : FCoAlg S P A) (f : A ~> B)
  : f =e g \o fmap f \o h -> f =e hylo g h.
Proof.
  intros H. unfold hylo, hylo_f. simpl.
  intros x. generalize x, (finite h x). clear x.
  fix Ih 2. intros x Fx. rewrite (H _). simpl. unfold comp. unfold fmap.
  destruct Fx as [x Fx]. simpl. destruct (h x) as [s_x c_x]. simpl in *.
  apply f_eq. simpl. split; [trivial|simpl; intros e d1 d2].
  rewrite (bool_irrelevance d2 d1). apply Ih. Guarded.
Qed.

Lemma hylo_univ_l S P {F : functor S P}
      A B {eA : equiv A} {eB : equiv B}
      (g : Alg S P B) (h : FCoAlg S P A) (f : A ~> B)
  : f =e hylo g h -> f =e g \o fmap f \o h.
Proof.
  intros H. rewrite H. clear H f. simpl. intros x. unfold comp.
  unfold hylo_f at 1. destruct (finite h x) as [x Fx]. simpl.
  destruct (h x) as [s_x c_x]. simpl in *.
  apply f_eq. unfold fmapA, comp, projT1, projT2, hylo_f.
  split; [trivial|simpl; intros e d1 d2]. rewrite (bool_irrelevance d1 d2).
  apply hylo_f_irr.
Qed.

Lemma hylo_univ S P {F : functor S P}
      A B {eA : equiv A} {eB : equiv B}
      (g : Alg S P B) (h : FCoAlg S P A) (f : A ~> B)
  : f =e hylo g h <-> f =e g \o fmap f \o h.
Proof. split;[apply hylo_univ_l|apply hylo_univ_r]. Qed.

Corollary hylo_unr S P {F : functor S P}
      A B {eA : equiv A} {eB : equiv B}
      (g : Alg S P B) (h : FCoAlg S P A)
  : hylo g h =e g \o fmap (hylo g h) \o h.
Proof. rewrite <-hylo_univ. reflexivity. Qed.

Lemma fin_out S P (F : functor S P) : forall x, FinF l_out x.
Proof. induction x as [s k Ih]. constructor. apply Ih. Qed.

Definition f_out S P (F : functor S P) : FCoAlg S P (LFix S P) :=
  exist _ _ (@fin_out S P F).
Arguments f_out {S P F}.

Lemma hylo_cata S P {F : functor S P} B {eB : equiv B} (g : Alg S P B)
  : cata g =e hylo g f_out.
Proof. rewrite hylo_univ. apply cata_univ. reflexivity. Qed.

Lemma hylo_ana  S P {F : functor S P} A {eA : equiv A} (h : FCoAlg S P A)
  : ana h =e hylo l_in h.
Proof. rewrite hylo_univ. apply ana_univ. reflexivity. Qed.

Lemma compA A B C D {eA : equiv A} {eB : equiv B}
      {eC : equiv C} {eD : equiv D}
      (f : C ~> D) (g : B ~> C) (h : A ~> B)
  : f \o (g \o h) =e (f \o g) \o h.
Proof. intros x. auto with ffix. Qed.

Lemma idKl A B {eA : equiv A} {eB : equiv B} (f : A ~> B)
  : f \o id =e f.
Proof. intros x. eauto with ffix. Qed.

Lemma idKr A B {eA : equiv A} {eB : equiv B} (f : A ~> B)
  : id \o f =e f.
Proof. intros x. eauto with ffix. Qed.

Lemma splitC A B C
      {eA : equiv A} {eB : equiv B} {eC : equiv C}
      (f1 f2 : B ~> C) (g1 g2 : A ~> B)
  : f1 =e f2 -> g1 =e g2 -> f1 \o g1 =e f2 \o g2.
Proof. intros ->->. reflexivity. Qed.

Lemma hylo_fusion_l S P {F : functor S P} A B C
      {eA : equiv A} {eB : equiv B} {eC : equiv C}
      (h1 : FCoAlg S P A) (g1 : Alg S P B) (g2 : Alg S P C) (f2 : B ~> C)
      (E2 : f2 \o g1 =e g2 \o fmap f2)
  : f2 \o hylo g1 h1 =e hylo g2 h1.
Proof.
  rewrite hylo_univ.
  rewrite fmap_comp.
  rewrite compA.
  rewrite <- E2.
  rewrite <- compA.
  rewrite <- compA.
  rewrite (compA g1).
  rewrite <- hylo_unr.
  reflexivity.
Qed.

Lemma hylo_fusion_r S P {F : functor S P} A B C
      {eA : equiv A} {eB : equiv B} {eC : equiv C}
      (h1 : FCoAlg S P B) (g1 : Alg S P C) (h2 : FCoAlg S P A)
      (f1 : A ~> B) (E1 : h1 \o f1 =e fmap f1 \o h2)
  : hylo g1 h1 \o f1 =e hylo g1 h2.
Proof.
  rewrite hylo_univ.
  rewrite fmap_comp.
  rewrite <- compA.
  rewrite <- compA.
  rewrite <- E1.
  rewrite compA.
  rewrite compA.
  rewrite <- hylo_unr.
  reflexivity.
Qed.

Lemma deforest S P {F : functor S P} A B C
      {eA : equiv A} {eB : equiv B} {eC : equiv C}
      (h1 : FCoAlg S P A) (g1 : Alg S P B) (h2 : FCoAlg S P B) (g2 : Alg S P C)
      (INV: h2 \o g1 =e id)
  : hylo g2 h2 \o hylo g1 h1 =e hylo g2 h1.
Proof.
  apply hylo_fusion_l.
  rewrite hylo_unr at 1.
  rewrite <- compA.
  rewrite INV.
  rewrite idKl.
  reflexivity.
  Restart.
  apply hylo_fusion_r.
  rewrite hylo_unr at 1.
  rewrite compA,compA,INV,idKr.
  reflexivity.
Qed.

Corollary cata_ana_hylo S P (F : functor S P)
          A B {eA : equiv A} {eB : equiv B}
          (g : Alg S P B) (h : FCoAlg S P A)
  : cata g \o ana h =e hylo g h.
Proof. rewrite hylo_cata,hylo_ana. apply deforest,l_out_in. Qed.


Require List.
Section ExQsort.

  (* Defining a tree *)

  (* shapes *)
  Inductive Ts A := | Leaf | Node (ELEM : A).
  Inductive Tp := | Lbranch | Rbranch. (* positions *)
  Definition t_dom A (s : Ts A) : Tp -> bool := (* position valid in shape? *)
    match s with
    | Node _ => fun _ =>true
    | _ => fun _ => false
    end.
  Instance tree_func A : functor (Ts A) Tp :=
    { dom := @t_dom  A
    }.

  Lemma dom_leaf_false A : elem_of (Leaf A) -> False.
  Proof. intros []. simpl in *. discriminate. Qed.
  Definition dom_leaf A B (x : elem_of (Leaf A)) : B :=
    False_rect _ (dom_leaf_false x).

  Definition a_leaf (A X : Type)
    : App (Ts A) Tp X := existT _ (Leaf A) (@dom_leaf A X).
  Definition a_node A X (x : A) (l r : X) : App (Ts A) Tp X :=
    existT _ (Node x) (fun p => match proj1_sig p with
                                | Lbranch => l
                                | Rbranch => r
                                end).

  Definition a_out A X (x : App (Ts A) Tp X)
    : option (A * X * X)
    := match x with
       | existT _ s k =>
         match s return (sig (fun x => t_dom s x = true) -> X) -> _ with
         | Leaf _ => fun _ => None
         | Node x =>
           fun k=>
             Some (x,
                   k (exist _ Lbranch eq_refl),
                   k (exist _ Rbranch eq_refl))
         end k
       end.
  (* end tree *)

  Definition m_merge (x : App (Ts nat) Tp (list nat)) : list nat :=
    match a_out x with
    | None => nil
    | Some (h, l, r) => Datatypes.app l (h :: r)
    end.
  Lemma m_merge_arr : forall x y, x =e y -> m_merge x =e m_merge y.
  Proof.
    intros [[|hx] kx] [[|hy] ky] [Hs Hk]; simpl in *; try discriminate; auto.
    specialize Hk with (d1:=eq_refl) (d2:=eq_refl).
    inversion_clear Hs.
    unfold m_merge. simpl. rewrite !Hk. reflexivity.
  Qed.
  Definition merge : Alg (Ts nat) Tp (list nat)
    := {| app := m_merge; f_eq := m_merge_arr |}.

  Definition m_split (x : list nat) : App (Ts nat) Tp (list nat) :=
    match x with
    | nil => a_leaf _ _
    | cons h t
      => a_node h
                (List.filter (fun x => Nat.leb x h) t)
                (List.filter (fun x => negb (Nat.leb x h)) t)
    end.
  Lemma m_split_arr : forall x y, x =e y -> m_split x =e m_split y.
  Proof. intros x y ->. auto with ffix. Qed.
  Definition c_split : CoAlg (Ts nat) Tp (list nat)
    := {| app := m_split; f_eq := m_split_arr |}.

  Lemma length_filter A (p : A -> bool) (l : list A) n :
    Nat.leb (length l) n = true ->
    Nat.leb (length (List.filter p l)) n = true.
  Proof with (simpl in *; try discriminate; auto).
    revert n.
    induction l as [|h t Ih]...
    intros [|n]...
    destruct (p h)...
    intros H. specialize (Ih n H). clear H.
    generalize dependent (length (List.filter p t)). intros m. revert n.
    induction m as [|m Ih]; intros n; auto.
    destruct n as [|n]; simpl in *; try discriminate. apply Ih.
  Qed.
  (* Needs to be defined, otherwise msort does not reduce!
   * UPDATE 12/09/2023 by DC: what's the nonsense above???
   *)
  Lemma split_fin : forall x, FinF c_split x.
  Proof.
    intros x. generalize (PeanoNat.Nat.leb_refl (List.length x)).
    generalize (length x) at 2. intros n. revert x.
    induction n as [|n Ih]; simpl;intros [|h t] H; simpl in *; try discriminate;
      constructor; simpl; intros e; try destruct (dom_leaf_false e).
    destruct e as [se ke].
    destruct se; simpl in *; clear ke; apply Ih, length_filter; trivial.
  Qed.

  Definition tsplit : FCoAlg (Ts nat) Tp (list nat)
    := exist _ c_split split_fin.


  (* YAY! quicksort in Coq as a divide-and-conquer "finite" hylo :-) *)
  (* UPDATE 12/09/2023 by DC: this used to be mergesort, and at some
   * point I simply changed the implementation ...
   *)
  Definition msort : list nat -> list nat := hylo merge tsplit.
End ExQsort.

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extract Inlined Constant Nat.leb => "(<=)".
Set Extraction TypeExpand.
(* Set Extraction Conservative Types. *)
Extraction Inline projT1.
Extraction Inline projT2.

Extraction Inline app.
Extraction Inline coalg.
Extraction Inline hylo.
Extraction Inline hylo_f.
Extraction Inline hylo_f_.

Extraction Inline merge.
Extraction Inline a_leaf.
Extraction Inline a_node.
Extraction Inline m_merge.
Extraction Inline m_split.
Extraction Inline a_out.
Extraction Inline c_split.
Extraction Inline tsplit.
Set Extraction Flag 2047.
(* Set Extraction Optimize. *)
Recursive Extraction msort.
Extraction "../extraction/test.ml" msort.
