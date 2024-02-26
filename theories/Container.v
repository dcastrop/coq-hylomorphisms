Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import HYLO.Equivalence.
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
Class Cont `{Esh : setoid Sh} `{Ep : setoid P} :=
  { valid : Sh * P ~> bool
  }.
Arguments Cont Sh {Esh} P {Ep}.

Record Pos `{Cont Sh P} (s : Sh) :=
  MkElem {
      val : P;
      Valid : valid (s, val) = true
    }.
Arguments Pos & {Sh _ P _ F} s : rename.
Arguments MkElem & {Sh _ P _ F s} val Valid : rename.
Arguments val & {Sh _ P _ F s} : rename.
Arguments Valid & {Sh _ P _ F s} : rename.

#[export] Instance PosSetoid `{Cont Sh P} (s : Sh) : setoid (Pos s).
Proof.
  apply (@MkSetoid _ (fun x y => val x =e val y)); auto with ffix.
  intros x y z; apply e_trans.
Defined.

Lemma pos_eq  `{Cont Sh P} (s : Sh) (p0 p1 : Pos s)
  : val p0 =e val p1 <-> p0 =e p1.
Proof. split; trivial. Qed.

Lemma elem_valid_irr `{Cont Sh P} (s1 s2 : Sh) (Eq : s1 =e s2)
  : forall e1 : Pos s1, exists e3 : Pos s2, val e1 =e val e3.
Proof.
  intros [v d1]. simpl. rewrite Eq in d1. exists (MkElem v d1). reflexivity.
Qed.

Record App `{F : Cont Sh P} `{setoid X} :=
  MkCont
    { shape : Sh;
      cont : Pos shape ~> X
    }.
Arguments App {Sh _ P _} F X {_}.
Arguments cont {Sh _ P _ F X _} a.
Arguments MkCont {Sh _ P _ F X _} shape cont.

Lemma cont_valid_irrelevant `{F : Cont Sh Po} `{setoid X} :
  forall (x : App F X) (e1 e2 : Pos (shape x)),
    e1 =e e2 -> cont x e1 =e cont x e2.
Proof. auto with ffix. Qed.

Inductive AppR `{F : Cont Sh P} `{e : setoid X} (x y : App F X) : Prop :=
  | AppR_ext
      (Es : shape x =e shape y)
      (Ek : forall e1 e2, val e1 =e val e2 -> cont x e1 =e cont y e2).
#[export]
  Hint Constructors AppR : ffix.

#[export]
  Instance App_setoid `{F : Cont Sh P} `{e : setoid X} : setoid (App F X).
Proof with eauto with ffix.
  apply (@MkSetoid _ (@AppR Sh _ P _ F X e)).
  - intros [shx kx]. constructor...
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
  (k k' : Pos s ~> X)
  : (forall x, k x =e k' x) -> AppR (MkCont s k) (MkCont s k').
Proof with simpl in *; auto with ffix.
  intros Heq. constructor...
  intros e1 e2. rewrite pos_eq. intros->. apply Heq.
Qed.

Definition fmapA `{F : Cont Sh P} `{setoid A} `{setoid B}
  (f : A ~> B) (x : App F A) : App F B
  := MkCont (shape x) (f \o cont x).

Lemma fmapA_eqF `{F : Cont Sh P} `{setoid A} `{setoid B} (f : A ~> B)
  : forall (x y : App F A), x =e y -> fmapA (F:= F) f x =e fmapA f y.
Proof with eauto with ffix.
  intros [sx kx] [sy ky] [Es Ek]. split; auto. intros. simpl in *.
  rewrite Ek; try reflexivity. exact H1.
Qed.

Definition fmapU `{F : Cont Sh P} `{setoid A} `{setoid B}
  (f : A ~> B) : App F A ~> App F B :=
  Eval unfold fmapA in MkMorph (fmapA_eqF f).

Lemma fmapU_eq `{F : Cont Sh P} `{eA : setoid A} `{eB : setoid B} :
  forall f g : A ~> B, f =e g -> fmapU (F:=F) f =e fmapU (F:=F) g.
Proof.
  intros f g Hfg [sh p]. simpl.
  apply cont_ext_eq.
  intros. apply Hfg.
Qed.

Definition fmap `{F : Cont Sh P} `{eA : setoid A} `{eB : setoid B} :
  (A ~> B) ~> App F A ~> App F B :=
  Eval unfold fmapU in MkMorph fmapU_eq.

Lemma fmap_id `{F : Cont Sh P} `{setoid A} : fmap (F:=F) (id (A:=A)) =e id.
Proof.
  intros []; constructor; try reflexivity; simpl in *.
  intros e1 e2 Hv. rewrite pos_eq in Hv. rewrite Hv. reflexivity.
Qed.

Lemma fmap_comp `{F : Cont Sh P} `{setoid A} `{setoid B} `{setoid C}
  (f : B ~> C) (g : A ~> B) : fmap (F:=F) (f \o g) =e fmap f \o fmap g.
Proof.
  intros []; constructor; try reflexivity; simpl.
  intros e1 e2 Hv. rewrite pos_eq in Hv. rewrite Hv. reflexivity.
Qed.


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
  Context `(C1 : Cont S1 P1) `(C2 : Cont S2 P2).
  Notation Ps := ((S1 * S2)%type).
  Notation Pp := ((P1 + P2)%type).
  Instance Prod : Cont Ps Pp.
  refine {| valid := {| app := fun x : Ps * Pp  =>
                               match snd x with
                               | inl p => valid (fst (fst x), p)
                               | inr p => valid (snd (fst x), p)
                               end |} |}.
  intros [[??]?][[??]p0] [[??]?]. simpl in *.
  destruct s1 as [s1|s1]; destruct p0 as [p0|p0]; try destruct H1.
  - rewrite H, H1. reflexivity.
  - rewrite H0, H1. reflexivity.
  Defined.
End Product.

(* Sum container *)
Section Sum.
  Context `(C1 : Cont S1 P1) `(C2 : Cont S2 P2).
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
  - rewrite E, F; reflexivity.
  - rewrite E, F; reflexivity.
  Defined.
End Sum.

Section Composition.
  Context `(F : Cont S1 P1) `(G : Cont S2 P2).

  Definition composeValid : App F S2 * (P1 * P2) ~> bool.
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
    intros [a [pa1 pa2]] [b [pb1 pb2]] [aRb [E1 E2]]; simpl in *.
    destruct aRb as [Es Ek].
    assert (Dab : valid (shape b, pb1) =e valid (shape a, pa1)).
    { apply app_eq. split; symmetry; trivial. }
    simpl in Dab. revert Dab.
    generalize (@eq_refl _ (valid (shape a, pa1))).
    generalize (valid (shape a, pa1)) at 2 3 4.  intros b0 e e'.
    generalize (@eq_refl _ (valid (shape b, pb1))).
    generalize (valid (shape b, pb1)) at 2 3.  intros b1 e''.
    assert (Eb : b1 = b0) by (rewrite <- e', <- e''; reflexivity).
    revert e''; rewrite Eb. clear Eb b1. intros e''.
    clear e'. rename e'' into e'.
    destruct b0; trivial; simpl. apply fold_eq.
    apply app_eq; split; trivial; simpl. apply Ek; trivial.
  Defined.

  #[export]
    Instance CompCont : Cont (App F S2) (P1 * P2) := { valid := composeValid }.
End Composition.
