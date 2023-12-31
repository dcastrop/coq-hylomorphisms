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

(* shapes *)
Inductive Ts A := | Leaf | Node (ELEM : A).
Inductive Tp := | Lbranch | Rbranch. (* positions *)
(* position valid in shape? *)
Definition t_dom A : Ts A * Tp ~> bool.
  refine {| app := fun x =>
                     match x with
                     | (Node _, _)  => true
                     | _            => false
                     end
         |}.
  intros [??] [??] [E1 E2]. simpl in *.  subst. auto.
Defined.
#[local]
  Instance TreeF (A : Type) : Container (Ts A) Tp :=
  { dom := t_dom A }.
Definition Tree A := LFix (TreeF A).

Lemma dom_leaf_false A : Pos (F:=TreeF A) (Leaf A) -> False.
Proof. intros []. simpl in *. discriminate. Qed.
Definition dom_leaf A B (x : Pos (F:=TreeF A) (Leaf A)) : B :=
  False_rect _ (dom_leaf_false x).

Definition a_leaf (A X : Type)
  : App (TreeF A) X := MkCont (Leaf A) (@dom_leaf A X).
Arguments a_leaf & {A X}.
Definition a_node A X (x : A) (l r : X) : App (TreeF A) X :=
  MkCont (Node x) (fun p => match val p with
                            | Lbranch => l
                            | Rbranch => r
                            end).
Arguments a_node & {A X}.

Definition e_lbranch A (x : A) : Pos (Node x) := MkElem Lbranch eq_refl.
Definition e_rbranch A (x : A) : Pos (Node x) := MkElem Rbranch eq_refl.

Definition a_out {A X : Type} : App (TreeF A) X ~> option (A * X * X).
  refine
    {| app :=
        fun x : App (TreeF A) X =>
          let (s, k) := x in
          match s return (Pos s -> X) -> option (A * X * X) with
          | Leaf _ => fun _ => None
          | Node x =>
              fun k : Pos (Node x) -> X =>
                Some (x, k (e_lbranch x), k (e_rbranch x))
          end k
    |}.
  intros [x Fx] [y Fy] [Sxy Kxy]. simpl in *. subst.
  destruct y; trivial.
  rewrite (Kxy (e_lbranch ELEM) (e_lbranch ELEM) eq_refl).
  rewrite (Kxy (e_rbranch ELEM) (e_rbranch ELEM) eq_refl).
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
