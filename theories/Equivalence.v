Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Logic.Eqdep_dec.
Require Export Setoid.

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

Reserved Notation "f =e g" (at level 70, no associativity).
#[universes(template)]
  Class equiv A : Type :=
  MkEquiv
    { eqRel : A -> A -> Prop;
      e_refl : forall x, eqRel x x;
      e_sym : forall x y, eqRel x y -> eqRel y x;
      e_trans : forall x y z, eqRel x y -> eqRel y z -> eqRel x z;
    }.

Notation "f =e g" := (eqRel f g).

Add Parametric Relation `{eq : equiv A} : A (@eqRel A eq)
    reflexivity proved by (@e_refl A eq)
    symmetry proved by (@e_sym A eq)
    transitivity proved by (@e_trans A eq)
      as ExtEq.

#[export] Hint Resolve e_refl : ffix.
#[export] Hint Resolve e_sym : ffix.
#[export] Hint Resolve e_trans : ffix.

#[export] Instance def_eq A : equiv A | 100 :=
  {| eqRel := @eq A;
     e_refl := @eq_refl A;
     e_sym := @eq_sym A;
     e_trans := @eq_trans A;
  |}.

#[export] Instance ext_eq (A : Type) `{eq_B : equiv B} : equiv (A -> B).
Proof with eauto with ffix.
  apply (@MkEquiv _ (fun f g =>forall x, eqRel (f x) (g x)))...
Defined.

#[export] Instance pair_eq `{eq_A : equiv A} `{eq_B : equiv B} : equiv (A * B).
Proof with eauto with ffix.
  apply (@MkEquiv _ (fun x y => fst x =e fst y /\ snd x =e snd y))...
  - intros x y [->->]...
  - intros x y z [->->]...
Defined.

#[export] Instance sum_eq `{eq_A : equiv A} `{eq_B : equiv B} : equiv (A + B).
Proof with eauto with ffix.
  apply (@MkEquiv _ (fun x y =>
                       match x, y with
                       | inl u, inl v => u =e v
                       | inr u, inr v => u =e v
                       | _, _ => False
                       end
                       ))...
  - intros []...
  - intros [x|x] [y|y]...
  - intros [x|x] [y|y] [z|z]...
    * intros [].
    * intros [].
Defined.

Class equivs (A : list Type) : Type.
#[export] Instance e_nil : equivs (@nil Type).
Defined.
#[export] Instance e_cons `{equiv A} `{equivs B} : equivs (A::B).
Defined.
