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

Notation a_leaf x := (MkCont (Leaf _ x) (@dom_leaf _ _ _ x)).
Notation a_node x l r :=
  (MkCont (Node _ x) (fun p => match val p with
                              | Lbranch => l
                              | Rbranch => r
                              end)).

Definition lnode_valid {L A} (x : Ts L A)
  : forall (n : A), x = Node L n -> valid (x, Lbranch) = true.
Proof. intros n ->. reflexivity. Qed.
Definition rnode_valid {L A} (x : Ts L A)
  : forall (n : A), x = Node L n -> valid (x, Rbranch) = true.
Proof. intros n ->. reflexivity. Qed.

Notation e_lbranch H := (MkElem Lbranch (lnode_valid H)).
Notation e_rbranch H := (MkElem Rbranch (rnode_valid H)).
Notation leftB  := (e_lbranch eq_refl).
Notation rightB := (e_rbranch eq_refl).

Definition a_out {L A X : Type} : App (TreeF L A) X ~> ITreeF L A X.
    refine
      {| app :=
          fun x : App (TreeF L A) X =>
            let (s, k) := x in
            match s as s' return s = s' -> ITreeF L A X with
            | Leaf _ x => fun _ => leaf x
            | Node _ n => fun E => node n (k (e_lbranch E)) (k (e_rbranch E))
            end eq_refl
      |}.
  intros [x Fx] [y Fy] [Sxy Kxy]. simpl in *. subst.
  destruct y; trivial; simpl.
  rewrite (Kxy leftB leftB); trivial.
  rewrite (Kxy rightB rightB); trivial.
Defined.

(* TODO: refactor into Utilities *)
Lemma length_filter A (p : A -> bool) (l : list A) :
  length (List.filter p l) <= length l.
Proof.
  induction l as [|h t Ih]; try apply le_n.
  simpl. destruct (p h); simpl.
  -  apply le_n_S, Ih.
  -  apply le_S, Ih.
Qed.

Lemma eta_pair A B (p : A * B) : p = (fst p, snd p).
Proof. destruct p; trivial. Qed.

Lemma wf_lt : well_founded lt.
Proof.
  intros x. constructor. revert x. fix Ih 1.
  intros [|x] y LT.
  - destruct (PeanoNat.Nat.nlt_0_r _ LT).
  - constructor. intros y' LT'. apply (Ih x). Guarded.
    rewrite PeanoNat.Nat.lt_succ_r in LT.
    apply (PeanoNat.Nat.lt_le_trans _ _ _ LT' LT).
Defined.
