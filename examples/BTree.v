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

Tactic Notation "|{" ident(x)  "~>" uconstr(T) "}|" :=
  refine {| app := fun x => T |};
  try (intros ??->; reflexivity);
  try (let H := fresh "H" in intros ?? H; simpl in H; subst; reflexivity);
  try (intros [??] [??] [E1 E2]; simpl in *;  subst; auto with ffix).


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
|{ x ~> match x with
     | (Node _ _, _)  => true
     | _            => false
     end
  }|.
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
  refine {|
      app := fun (x : App (TreeF L A) X) =>
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

Inductive itree L A := | i_leaf (l : L) | i_node (x : A) (l r : itree L A).
Definition to_tree {L A} : itree L A ~> App (TreeF L A) (itree L A).
|{ x ~>
     match x with
     | i_leaf _ l => a_leaf l
     | i_node n l r => a_node n l r
     end
  }|.
Defined.

Lemma to_tree_rec {L A} : RecP (@to_tree L A).
Proof.
  intros x. induction x as [l|n l Ihl r Ihr]; constructor; simpl; intros e.
  - apply (dom_leaf _ e).
  - destruct (val e); trivial.
Defined.

Definition fto_tree {L A}: RCoalg (TreeF L A) (itree L A) := Rec to_tree_rec.

Definition itree_to_tree {L A} : itree L A ~> Tree L A :=
  rana fto_tree.

Definition to_itree {L A} : App (TreeF L A) (itree L A) ~> itree L A.
|{ x ~>
     match a_out x with
     | leaf l => i_leaf _ l
     | node n l r => i_node n l r
     end
  }|.
Defined.
Definition tree_to_itree {L A} : Tree L A ~> itree L A
  := cata to_itree.

Lemma tree_itree_iso1 {L A} : itree_to_tree (L:=L) (A:=A) \o tree_to_itree =e id.
  Opaque to_tree_rec.
  Opaque cata.
  Opaque rana.
  intros x. unfold tree_to_itree, itree_to_tree.
  induction x as [[[|n] kx] Ih]; rewrite cata_unfold, rana_unfold; simpl in *.
  - split; trivial. intros e. apply (dom_leaf _ e).
  - split; trivial. intros [[|] V1] [v2 V2]; simpl.
    + intros <-. rewrite elem_val_eq with (e1:=leftB) (e2:= {|val := Lbranch; Valid := V2|}); trivial.
    + intros <-. rewrite elem_val_eq with (e1:=rightB) (e2:= {|val := Rbranch; Valid := V2|}); trivial.
Qed.

Lemma tree_itree_iso2_ {L A}
  : cata to_itree \o rana fto_tree =e id (A:=itree L A).
  rewrite cata_ana_hylo. Opaque hylo. simpl. intros x.
  induction x as [l|n l Ihl r Ihr]; rewrite hylo_unr; simpl; trivial.
  rewrite Ihl, Ihr. reflexivity.
Qed.

(* For some reason unfolding does not work ...? *)
Lemma tree_itree_iso2 {L A}
  : tree_to_itree \o itree_to_tree =e id (A:=itree L A).
  exact tree_itree_iso2_.
Qed.

(* TODO: refactor into Utilities *)

Lemma eta_pair A B (p : A * B) : p = (fst p, snd p).
Proof. destruct p; trivial. Qed.

Lemma wf_lt : well_founded lt.
Proof.
  cut (forall x y, y < x -> Acc lt y).
  - intros H x. apply (H (S x) x), PeanoNat.Nat.lt_succ_diag_r.
  - fix Ih 1. intros [|x] y LT.
    + destruct (PeanoNat.Nat.nlt_0_r _ LT).
    + constructor. intros y' LT'. apply (Ih x). Guarded.
      rewrite PeanoNat.Nat.lt_succ_r in LT.
      apply (PeanoNat.Nat.lt_le_trans _ _ _ LT' LT).
Defined.
