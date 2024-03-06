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
Lemma nil_uninhabited {H B} (x : Pos (F:=ListF H) (@s_nil H)) : B x.
  apply (False_rect _ (dom_nil_false x)).
Defined.
Hint Extern 0 => (apply nil_uninhabited) : ffix.

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
Defined.

Definition ilist_alg {A} : App (ListF A) (list A) ~> list A.
|{ x : (App (ListF A) (list A)) ~> (let (s, k) := x in
     match s as s' return s = s' -> list A with
     | s_nil => fun _ => nil
     | s_cons h => fun E => cons h (get_tail k E)
     end eq_refl)
}|.
Defined.

Definition ilist_coalg {A} : list A ~> App (ListF A) (list A).
|{ x : (list A) ~>
         match x with
         | nil => a_nil
         | cons h t => a_cons h t
         end
}|.
Defined.
Lemma ilist_coalg_rec {A} : RecP (@ilist_coalg A).
Proof. intros x; induction x; constructor; auto with ffix. Qed.

Canonical Structure ilist_rcoalg {A} := Rec (@ilist_coalg_rec A).

Definition ilist_to_List {A} : list A ~> List A := rana ilist_coalg.
Definition List_to_ilist {A} : List A ~> list A := cata ilist_alg.

Lemma ilist_List_iso1 {A} : @ilist_to_List A \o List_to_ilist =e id.
Proof.
  unfold ilist_to_List, List_to_ilist, List. intros x.
  Opaque eqRel rana cata LFixR.
  induction x as [[[|h] kx] Ih];
    rewrite rana_unfold, cata_unfold; simpl in *; constructor; auto with ffix.
  - simpl in *. intros e1. destruct (dom_nil_false e1).
  - simpl in *. intros [[] V1] [[] V2] E. simpl in *.
    rewrite (bool_irrelevance V2 (p_cons (@eq_refl _ (s_cons h)))).
    apply Ih.
    Transparent eqRel rana cata LFixR.
Qed.

Lemma ilist_List_iso {A} : @List_to_ilist A \o ilist_to_List =e id.
Proof.
  unfold ilist_to_List, List_to_ilist, List.
  rewrite cata_ana_hylo. symmetry. apply hylo_univ.
  rewrite fmap_id, idKr. intros [|h t]; auto with ffix.
Qed.

Definition Lmap {A B} (f : A ~> B) : List A ~> List B :=
  everywhere (natural_list f).

(* TODO: get rid of all of these with canonical structures *)
Definition ILmap {A B} (f : A ~> B) : list A ~> list B.
|{ x ~> (List.map f x) }|.
Defined.

Lemma ifmap_fmap {A B} (f : A ~> B) :
  ilist_coalg (A:=B) \o ILmap f
  =e natural (natural_list f) \o fmap (ILmap f) \o ilist_coalg.
Proof.
  intros []; simpl in *; auto with ffix. constructor; simpl; auto with ffix.
  intros e; destruct (dom_nil_false e).
Qed.

Lemma fmap_ifmap {A B} (f : A ~> B) :
  ILmap f \o ilist_alg (A:=A)
  =e ilist_alg \o natural (natural_list f) \o fmap (ILmap f).
Proof.
  intros [[|h] k]; simpl in *; auto with ffix.
  rewrite (bool_irrelevance (map_shape_is_nt _) (p_cons eq_refl)).
  reflexivity.
Qed.

Lemma list_map_nat {A B} (f : A ~> B) :
  Lmap f \o ilist_to_List =e ilist_to_List \o ILmap (app f).
Proof.
  unfold ilist_to_List, List, Lmap, everywhere.
  rewrite <- hylo_cata, cata_ana_hylo, hylo_ana. symmetry.
  apply hylo_univ. rewrite hylo_unr at 1. rewrite <- !compA.
  rewrite ifmap_fmap, <- !compA. rewrite (compA (fmap _)).
  unfold natural. rewrite <- eta_is_natural. rewrite <- !compA.
  rewrite (compA (fmap _)), <- fmap_comp, !compA.
  reflexivity.
Qed.

Lemma list_ww2 {A B} (f : A ~> B) :
  List_to_ilist \o Lmap f  =e ILmap f \o List_to_ilist.
Proof.
  unfold List_to_ilist, Lmap, List, everywhere.
  rewrite hylo_map_shift, <- hylo_ana,cata_ana_hylo, hylo_cata. symmetry.
  apply hylo_univ. rewrite <- !compA.
  rewrite (compA _ (natural (natural_list f)) l_out).
  rewrite <- natural_fmap, fmap_comp, !compA.
  rewrite <- fmap_ifmap. rewrite <- !compA.
  rewrite (compA ilist_alg _ l_out). rewrite hylo_unr at 1. reflexivity.
Qed.
