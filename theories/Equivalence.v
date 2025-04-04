Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

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
Class setoid A : Type :=
  MkSetoid
    { eqRel : A -> A -> Prop;
      e_refl : forall x, eqRel x x;
      e_sym : forall x y, eqRel x y -> eqRel y x;
      e_trans : forall x y z, eqRel x y -> eqRel y z -> eqRel x z;
    }.

Notation "f =e g" := (eqRel f g).

Add Parametric Relation `{eq : setoid A} : A (@eqRel A eq)
    reflexivity proved by (@e_refl A eq)
    symmetry proved by (@e_sym A eq)
    transitivity proved by (@e_trans A eq)
      as ExtEq.

#[export] Hint Resolve e_refl : ffix.
#[export] Hint Resolve e_sym : ffix.
#[export] Hint Resolve e_trans : ffix.

(* Import Module when standard equality is needed *)
#[export] Instance def_eq A : setoid A | 100 :=
{| eqRel := @eq A;
  e_refl := @eq_refl A;
  e_sym := @eq_sym A;
  e_trans := @eq_trans A;
|}.

#[export] Instance ext_eq (A : Type) `{eq_B : setoid B} : setoid (A -> B).
Proof with eauto with ffix.
  apply (@MkSetoid _ (fun f g =>forall x, eqRel (f x) (g x)))...
Defined.

#[export] Instance pair_eq `{eq_A : setoid A} `{eq_B : setoid B} : setoid (A * B).
Proof with eauto with ffix.
  apply (@MkSetoid _ (fun x y => fst x =e fst y /\ snd x =e snd y))...
  - intros x y [->->]...
  - intros x y z [->->]...
Defined.

Add Parametric Morphism `{eA : setoid A} `{eB : setoid B}
  : (@Datatypes.pair A B)
    with signature
    (eqRel (A:=A))
      ==> (eqRel (A:=B))
      ==> (eqRel (A:=A * B))
      as coqPairMorphism.
Proof.
  intros ?? Efg x y Exy.
  split; [apply Efg| apply Exy].
Qed.

#[export] Instance sum_eq `{eq_A : setoid A} `{eq_B : setoid B} : setoid (A + B).
Proof with eauto with ffix.
  apply (@MkSetoid _ (fun x y =>
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

#[export] Instance prop_eq : setoid Prop.
Proof with eauto with ffix.
  apply (@MkSetoid _ (fun p q => p <-> q)).
  - intros. split; trivial.
  - intros. rewrite H; split;  trivial.
  - intros. rewrite H; trivial.
Defined.

#[export] Instance pred_sub `{eA : setoid A} {P : A -> Prop}
  : setoid {a : A | P a}.
Proof with eauto with ffix.
  apply (@ MkSetoid _ (fun px py => proj1_sig px =e proj1_sig py))...
Defined.

Class equivs (A : list Type) : Prop.
#[export] Instance e_nil : equivs (@nil Type).
Defined.
#[export] Instance e_cons `{setoid A} `{equivs B} : equivs (A::B).
Defined.
