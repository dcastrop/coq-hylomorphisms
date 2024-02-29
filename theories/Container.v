Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import HYLO.Equivalence.
Import StdEquiv.
Require Import HYLO.Morphism.


(** The justification why the class below this comment defines a Container can be
  * found later, with the definitions: App, fmapA, etc.
  * - [S] is the type of "shapes" of this Cont
  * - [P] is the type of "positions" in a shape
  * - [valid] determines whether a position is valid in a shape
  *
  * It is defined as a class to help extract cleaner code to OCaml.
  * An alternative definition, closer to the literature, would be to have
  * a record,
  * [ Record Cont :=
      { shape : Type;
        position : Type;
        valid : shape -> position -> bool;
      }
    ]
  * use dependent types,
  * [ Record Cont :=
      { shape : Type;
        position : shape -> Type;
      }
    ]
  * or even a straightforward "strict-positivisation" of an actual functor [F]:
  * [ Record Apply (F : Type -> Type) (X : Type) :=
      { witness : Type;
        shape : F witness;
        position : witness -> X;
      }
    ]
  * However, these alternatives would lead to lots of [Obj.magic] in the
  * generated OCaml code, and a priority of this experiment was extracting
  * "somewhat reasonable/clean" OCaml code.
  *)
Class Cont `{Esh : setoid Sh} (P : Type) :=
  { valid : Sh * P ~> bool
  }.
Arguments Cont Sh {Esh} P.

Coercion is_true b : Prop := b = true.

Record Pos `{Cont Sh P} (s : Sh) :=
  MkElem {
      val : P;
      Valid : valid (s, val)
    }.
Arguments Pos & {Sh _ P F} s : rename.
Arguments MkElem & {Sh _ P F s} val Valid : rename.
Arguments val & {Sh _ P F s} : rename.
Arguments Valid & {Sh _ P F s} : rename.

Lemma elem_val_eq `{Cont Sh P} (s : Sh) (e1 e2 : Pos s)
  : val e1 = val e2 -> e1 = e2.
Proof.
  destruct e1 as [v1 d1], e2 as [v d2]; simpl in *.
  intros; subst. rewrite (bool_irrelevance d1 d2). auto.
Qed.

Lemma elem_valid_irr `{Cont Sh P} (s1 s2 : Sh) (Eq : s1 =e s2)
  : forall e1 : Pos s1, exists e3 : Pos s2, val e1 = val e3.
Proof.
  intros [v d1]. simpl.
  assert (d2 : valid (s2, v) =e true).
  { rewrite <- d1. apply app_eq. split; simpl; auto with ffix. }
  simpl in *.
  exists (MkElem v d2); auto.
Qed.

Record App `{F : Cont Sh P} (X : Type) :=
  MkCont
    { shape : Sh;
      cont : Pos shape -> X
    }.
Arguments App {Sh _ P} F X.
Arguments cont {Sh _ P F X} a k.
Arguments MkCont {Sh _ P F X} shape cont.

Lemma cont_valid_irrelevant `{F : Cont Sh Po} (X : Type) :
  forall (x : App F X) (e1 e2 : Pos (shape x)),
    val e1 = val e2 -> cont x e1 = cont x e2.
Proof.
  intros [s p]. simpl. intros [e1 d1] [e2 d2]. simpl. intros Eq. subst.
  rewrite (bool_irrelevance d1 d2).
  reflexivity.
Qed.

Inductive AppR `{F : Cont Sh P} (X : Type) {e : setoid X}
           (x y : App F X) : Prop :=
  | AppR_ext
      (Es : shape x =e shape y)
      (Ek : forall e1 e2, val e1 = val e2 -> cont x e1 =e cont y e2).
#[export]
  Hint Constructors AppR : ffix.

#[export]
  Instance App_setoid `{F : Cont Sh P} `{e : setoid X} : setoid (App F X).
Proof with eauto with ffix.
  apply (@MkSetoid _ (@AppR Sh _ P F X e)).
  - intros [shx kx]. constructor...
    simpl.  intros [x1 d1] [x2 d2] Eq. simpl in *. subst.
    rewrite (bool_irrelevance d1 d2).
    reflexivity.
  - intros x y [Sxy Exy]. split...
  - intros x y z [Sxy Exy] [Syz Eyz]; simpl; split.
    * rewrite Sxy...
    * intros e1 e2 V1.
      destruct (elem_valid_irr Sxy e1) as [e3 V2].
      apply (e_trans (Exy e1 e3 V2)), Eyz.
      rewrite <- V2. trivial.
Defined.

Lemma fold_eq A (x y : A) : x =e y -> x = y.
Proof. trivial. Qed.

Lemma cont_ext_eq `{F : Cont Sh P} (s : Sh) `{setoid X}
  (k k' : Pos s -> X)
  : (forall x, k x =e k' x) -> AppR (MkCont s k) (MkCont s k').
Proof with simpl in *; auto with ffix.
  intros Heq. constructor...
  intros e1 e2 Hv. rewrite (elem_val_eq Hv)...
Qed.

Definition fmapA `{F : Cont Sh P} `{setoid A} `{setoid B}
  (f : A -> B) (x : App F A) : App F B
  := MkCont (shape x) (fun e => f (cont x e)).

Lemma fmapA_eqF `{F : Cont Sh P} `{setoid A} `{setoid B} (f : A ~> B)
  : forall (x y : App F A), x =e y -> fmapA (F:= F) f x =e fmapA f y.
Proof with eauto with ffix.
  intros [sx kx] [sy ky] [Es Ek]. split; auto. intros.  apply app_eq. auto.
Qed.

Notation fmapU f :=
  ({| app := fun x => MkCont (shape x) (fun e => f (cont x e));
     app_eq := fmapA_eqF f
   |}).

Lemma fmapU_eq `{F : Cont Sh P} `{eA : setoid A} `{eB : setoid B} :
  forall f g : A ~> B, f =e g -> fmapU f =e fmapU g.
Proof.
  intros f g Hfg [sh p]. simpl.
  apply cont_ext_eq.
  intros. apply Hfg.
Qed.

Definition fmap `{F : Cont Sh P} `{eA : setoid A} `{eB : setoid B} :
  (A ~> B) ~> App F A ~> App F B := MkMorph fmapU_eq.

Lemma fmap_id `{F : Cont Sh P} `{setoid A} : fmap (F:=F) (id (A:=A)) =e id.
Proof. intros []; reflexivity. Qed.

Lemma fmap_comp `{F : Cont Sh P} `{setoid A} `{setoid B} `{setoid C}
  (f : B ~> C) (g : A ~> B) : fmap (F:=F) (f \o g) =e fmap f \o fmap g.
Proof. intros []. reflexivity. Qed.


(* Polynomial functors as containers *)

(* Identity container *)
#[export] Instance Id : Cont unit unit.
refine {| valid := {| app := fun _ => true|} |}.
intros. reflexivity.
Defined.

(* Constant container *)
#[export] Instance K A : Cont A False.
refine {| valid := {| app := fun x : A * False => match snd x with end |} |}.
intros. destruct (snd x).
Defined.

(* Product container *)
Section Product.
  Context `{setoid S1} `{setoid S2} (P1 P2 : Type).
  Context (C1 : Cont S1 P1) (C2 : Cont S2 P2).
  Notation Ps := ((S1 * S2)%type).
  Notation Pp := ((P1 + P2)%type).
  Instance Prod : Cont Ps Pp.
  refine {| valid := {| app := fun x : Ps * Pp  =>
                               match snd x with
                               | inl p => valid (fst (fst x), p)
                               | inr p => valid (snd (fst x), p)
                               end |} |}.
  intros [[??]?][[??]p0] [[??]?]. simpl in *; subst.
  destruct p0 as [p|p].
  - apply fold_eq, app_eq. simpl; split; trivial.
  - apply fold_eq, app_eq. simpl; split; trivial.
  Defined.
End Product.

(* Sum container *)
Section Sum.
  Context `{setoid S1} `{setoid S2} (P1 P2 : Type).
  Context (C1 : Cont S1 P1) (C2 : Cont S2 P2).
  Notation Ps := ((S1 + S2)%type).
  Notation Pp := ((P1 + P2)%type).
  Instance Sum : Cont Ps Pp.
  refine {| valid := {| app := fun x : Ps * Pp  =>
                               match fst x, snd x with
                               | inl s, inl p => valid (s, p)
                               | inr s, inr p => valid (s, p)
                               | _, _ => false
                               end |} |}.
  intros [[?|?][?|?]] [[?|?][?|?]] [E F];
    simpl in *; subst; try (inversion F); try (inversion E); trivial.
  - apply fold_eq, app_eq. simpl; split; trivial.
  - apply fold_eq, app_eq. simpl; split; trivial.
  Defined.
End Sum.

Section Composition.
  Context `(F : Cont S1 P1) `(G : Cont S2 P2).

  Definition composeValid :
    @morph (App F S2 * (P1 * P2))
      (pair_eq (eq_B := def_eq (P1 * P2))) bool (def_eq bool).
    refine
      {| app :=
          fun (sp : App F S2 * (P1 * P2)) =>
            let (s , p12) := sp in
            let (p1 , p2) := p12 in
            match valid (shape s, p1) as b
                  return valid (shape s, p1) = b -> bool
            with
            | true => fun H =>
                        let e := MkElem p1 H in
                        let kp := cont s e in
                        valid (kp, p2)
            | false => fun _ => false
            end eq_refl
      |}.
    intros [a [pa1 pa2]] [b [pb1 pb2]] [aRb E12]; simpl in *.
    inversion E12. rename H0 into E1. rename H1 into E2.
    destruct aRb as [Es Ek].
    assert (Dab : valid (shape a, pa1) =e valid (shape b, pb1)).
    { apply app_eq. split; trivial. }
    simpl in Dab. subst.
    generalize (@eq_refl _ (valid (shape a, pb1))).
    generalize (@eq_refl _ (valid (shape b, pb1))).
    revert Dab.
    generalize (valid (shape a, pb1)) at 1 3 4. intros []; simpl in *.
    + generalize (valid (shape b, pb1)) at 1 3 4. intros []; try discriminate.
      intros _ d1 d2. apply fold_eq, app_eq. split; simpl in *; trivial.
      apply Ek; trivial.
    + generalize (valid (shape b, pb1)) at 1 3 4. intros []; try discriminate.
      trivial.
  Defined.

  #[export]
    Instance CompCont : Cont (App F S2) (P1 * P2) := { valid := composeValid }.
End Composition.

Section NaturalTransformation.
  Context `(F : Cont S1 P1) `(G : Cont S2 P2).

  Variable eta_S : S1 ~> S2.
  Variable eta_P : P2 -> P1.
  Variable eta_C : forall s p, valid (eta_S s, p) -> valid (s, eta_P p).

  Definition eta_Pos : forall s, Pos (eta_S s) -> Pos s
    := fun _ p => {| val := eta_P (val p); Valid := eta_C (Valid p) |}.

  Definition eta_ {X} : App F X -> App G X :=
    fun x => {| shape := eta_S (shape x); cont := fun p => cont x (eta_Pos p) |}.
  Lemma eta_morph `{setoid X} : forall x y, x =e y -> @eta_ X x =e @eta_ X y.
  Proof.
    intros [sx kx] [sy ky] [Es Ek]. unfold eta_. simpl in *.
    constructor; simpl; rewrite ?Es; auto with ffix.
    intros e1 e2 Ep. apply Ek.
    destruct e1 as [v1 V1], e2 as [v2 V2]; simpl in *; subst; trivial.
  Qed.
  Definition eta `{setoid X} : App F X ~> App G X :=
    Eval unfold eta_, eta_Pos in MkMorph eta_morph.

  Context `{setoid X} `{setoid Y}.
  Lemma eta_is_eta : forall (f : X ~> Y), @eta Y _ \o fmap f =e fmap f \o @eta X _.
  Proof.
    intros f [sx kx]. constructor; simpl; auto with ffix.
    intros e1 e2 Hv; apply app_eq; simpl.
    destruct e1 as [p1 V1], e2 as [p2 V2]; simpl in *.
    revert V2. rewrite <- Hv. intros V2.
    rewrite (bool_irrelevance V1 V2). reflexivity.
  Qed.
End NaturalTransformation.

Definition eta1 `{F : Cont S1 P} `{G : Cont S2 P}
  (f : S1 ~> S2) (H : forall s p, valid (f s, p) -> valid (s, p)) `{setoid X} :
  App F X ~> App G X := @eta _ _ _ _ _ _ _ _ f id H X _.

Arguments eta1 {S1}%type_scope {Esh} {P}%type_scope {F} {S2}%type_scope {Esh0 G} f H {X}%type_scope {H0}.
