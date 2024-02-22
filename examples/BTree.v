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

Inductive ITreeF L N X := leaf (ELEM : L) | node (ELEM : N) (LB RB : X).
Arguments leaf & {L N X} ELEM.
Arguments node & {L N X} ELEM LB RB.

(* shapes *)
Inductive Ts L A := | Leaf (ELEM : L) | Node (ELEM : A).
Inductive Tp := | Lbranch | Rbranch. (* positions *)
(* position valid in shape? *)
Definition t_dom {L A} : Ts L A * Tp ~> bool.
  refine {| app := fun x =>
                     match x with
                     | (Node _ _, _)  => true
                     | _            => false
                     end
         |}.
  intros [??] [??] [E1 E2]. simpl in *.  subst. auto.
Defined.
#[local]
  Instance TreeF (L A : Type) : Cont (Ts L A) Tp :=
  { valid := @t_dom L A }.
Definition Tree L A := LFix (TreeF L A).

Lemma dom_leaf_false L A (x : L) : Pos (F:=TreeF L A) (Leaf A x) -> False.
Proof. intros []. simpl in *. discriminate. Qed.
Definition dom_leaf L A B (e : L) (x : Pos (F:=TreeF L A) (Leaf A e)) : B :=
  False_rect _ (dom_leaf_false x).

Definition a_leaf {L A X : Type} (x : L)
  : App (TreeF L A) X := MkCont (Leaf A x) (@dom_leaf L A X x).
Arguments a_leaf & {L A X}.
Definition a_node L A X (x : A) (l r : X) : App (TreeF L A) X :=
  MkCont (Node _ x) (fun p => match val p with
                            | Lbranch => l
                            | Rbranch => r
                            end).
Arguments a_node & {L A X} x l r.

Definition e_lbranch {L A} (x : A) : Pos (Node L x) := MkElem Lbranch eq_refl.
Arguments e_lbranch & {L A x}.
Definition e_rbranch {L A} (x : A) : Pos (Node L x) := MkElem Rbranch eq_refl.
Arguments e_rbranch & {L A x}.


Definition a_out {L A X : Type} : App (TreeF L A) X ~> ITreeF L A X.
    refine
      {| app :=
          fun x : App (TreeF L A) X =>
          let (s, k) := x in
          match s return (Pos s -> X) -> ITreeF L A X with
          | Leaf _ x => fun _ => leaf x
          | Node _ n => fun k => node n (k e_lbranch) (k e_rbranch)
          end k
      |}.
  intros [x Fx] [y Fy] [Sxy Kxy]. simpl in *. subst.
  destruct y; trivial.
  rewrite (Kxy e_lbranch e_lbranch eq_refl).
  rewrite (Kxy e_rbranch e_rbranch eq_refl).
  reflexivity.
Defined.

(* TODO: refactor Utilities for QSort *)
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
