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

Definition nt_shape {L L' A A'} (f : L ~> L') (g : A ~> A') : Ts L A ~> Ts L' A'.
|{
    x ~> match x with
                    | Leaf _ l => Leaf _ (f l)
                    | Node _ n => Node _ (g n)
                    end
  }|.
Defined.

Lemma nt_shape_is_nat {L L' A A'} (f : L ~> L') (g : A ~> A')
  : NaturalIn (TreeF L A) (TreeF L' A') (nt_shape f g).
Proof. intros [l|n] p; trivial. Qed.

Canonical Structure nt_tree {L L' A A'} (f : L ~> L') (g : A ~> A')
  : naturalM (TreeF L A) (TreeF L' A')
  := {| natT := nt_shape f g; natC := @nt_shape_is_nat _ _ _ _ f g |}.

Definition map_tree {L L' A A'} (f : L ~> L') (g : A ~> A')
  : LFix (TreeF L A) ~> LFix (TreeF L' A') :=
  everywhere (nt_shape f g).

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

Notation e_lbranch k H := (k (MkElem Lbranch (lnode_valid H))).
Notation e_rbranch k H := (k (MkElem Rbranch (rnode_valid H))).
Notation leftB  k := (e_lbranch k eq_refl).
Notation rightB k := (e_rbranch k eq_refl).

Definition posL {A} (h : A) : Pos (Node unit h) :=
  MkElem Lbranch eq_refl.
Definition posR {A} (h : A) : Pos (Node unit h) :=

  MkElem Rbranch eq_refl.

Definition a_out {L A X : Type} : App (TreeF L A) X ~> ITreeF L A X.
|{ x : (App (TreeF L A) X) ~> (
               let (s, k) := x in
               match s as s' return s = s' -> ITreeF L A X with
               | Leaf _ x => fun _ => leaf x
               | Node _ n => fun E => node n (e_lbranch k E) (e_rbranch k E)
               end eq_refl
         )
}|.
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
Definition tree_to_itree {L A} : Tree L A ~> itree L A := cata to_itree.

Lemma tree_itree_iso1 {L A} : itree_to_tree (L:=L) (A:=A) \o tree_to_itree =e id.
  Opaque to_tree_rec.
  Opaque cata.
  Opaque rana.
  intros x. unfold tree_to_itree, itree_to_tree.
  induction x as [[[|n] kx] Ih]; rewrite cata_unfold, rana_unfold; simpl in *.
  - split; trivial. intros e. apply (dom_leaf _ e).
  - split; trivial. intros [[|] V1] [v2 V2]; simpl.
    + intros <-. rewrite (bool_irrelevance V2 (lnode_valid eq_refl)). trivial.
    + intros <-. rewrite (bool_irrelevance V2 (rnode_valid eq_refl)). trivial.
Qed.

(* For some reason [Tree] needs unfolding ... *)
Lemma tree_itree_iso2 {L A}
  : tree_to_itree \o itree_to_tree =e id (A:=itree L A).
  unfold tree_to_itree, itree_to_tree, Tree. rewrite cata_ana_hylo.
  symmetry. rewrite hylo_univ, fmap_id, idKr. intros[]; simpl; trivial.
Qed.
