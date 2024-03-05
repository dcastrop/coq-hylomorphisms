Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import HYLO.Equivalence.
Require Import HYLO.Morphism.
Require Import HYLO.Container.
Require Import HYLO.Algebra.
Require Import HYLO.Coalgebra.
Require Import HYLO.FCoalgebra.
Require Import HYLO.Hylo.

Require List.

(* Defining a tree *)
Unset Auto Template Polymorphism.

Inductive IListF H T := i_nil | i_cons (h : H) (t : T).
Arguments i_nil  & {H T}.
Arguments i_cons & {H T} h t.

(* shapes *)
Inductive Lshape H := | s_nil | s_cons (h : H).
Arguments s_nil & {H}.
Definition Lpos := unit. (* positions *)
(* position valid in shape? *)

Definition l_valid {H} : Lshape H * Lpos ~> bool.
|{ x ~> match x with
     | (s_cons _, _)  => true
     | _              => false
     end
}|.
Defined.

#[local]
Instance ListF (H : Type) : Cont (Lshape H) Lpos := { valid := @l_valid H }.

Definition List H := LFix (ListF H).

Definition l_map_shape {H H'} (f : H ~> H') : Lshape H ~> Lshape H'.
|{x ~> match x with | s_nil => s_nil | s_cons h => s_cons (f h) end}|.
Defined.

Lemma map_shape_is_nt {H H'} (f : H ~> H')
  : NaturalIn (ListF H) (ListF H') (l_map_shape f).
Proof. intros [|n] p; trivial. Qed.

Canonical Structure natural_list {H H'} (f : H ~> H')
  : naturalM (ListF H) (ListF H')
  := {| natT := l_map_shape f; natC := @map_shape_is_nt _ _ f |}.

Lemma dom_nil_false H : Pos (F:=ListF H) (@s_nil H) -> False.
Proof. intros []. simpl in *. discriminate. Qed.
Definition nil_uninhabited {H B} (x : Pos (F:=ListF H) (@s_nil H)) : B :=
  False_rect _ (dom_nil_false x).

Notation a_nil := (MkCont (@s_nil _) (@nil_uninhabited _ _)).
Notation a_cons h t := (MkCont (s_cons h) (fun _ => t)).

Local Definition a_in {H X : Type} : IListF H X ~> App (ListF H) X.
|{ x ~> match x with
     | i_nil => a_nil
     | i_cons h t => a_cons h t
     end
  }|.
Defined.

Lemma p_cons {H s} {h : H} : s = s_cons h -> valid(s, tt).
Proof. intros->. reflexivity. Qed.

Notation get_tail k E := (k (MkElem tt (p_cons E))).

Local Definition a_out {H X : Type} : App (ListF H) X ~> IListF H X.
|{ x : (App (ListF H) X) ~> (
           let (s, k) := x in
           match s as s' return s = s' -> IListF H X with
           | s_nil => fun E => i_nil
           | s_cons h => fun E => i_cons h (get_tail k E)
           end eq_refl
         )}|.
destruct shape0; auto with ffix.
apply Logic.f_equal, E2; trivial.
Defined.
