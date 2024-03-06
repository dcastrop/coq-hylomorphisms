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

Require Import Util.Utils.

Require Import Examples.BTree.
Require Import Examples.CList.

Require Import List.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.

(** Example 1 from shortcut fusion in calc form [length \o map f \o append ys] *)
Definition tau_alg_ {A} `{setoid B} (l : list A) (a : Alg (ListF A) B)
  : App (ListF A) B -> B :=
  fun x =>
    match x with
    | MkCont sx kx =>
        match sx with
        | s_nil => fun _ => (hylo a ilist_coalg) l
        | s_cons h => fun kx => a (MkCont (s_cons h) kx)
        end kx
    end.

Lemma tau_alg_morph {A} `{setoid B} (l : list A) (a : Alg (ListF A) B) :
  forall x y, x =e y -> tau_alg_ l a x =e tau_alg_ l a y.
Proof.
  intros [sx kx] [sy ky] [Sxy Kxy]; simpl in *; subst.
  destruct sy as [|h]; simpl.
  reflexivity.
  apply app_eq.
  constructor; auto with ffix.
Qed.

Definition tau_alg {A} `{setoid B} (ys : list A) (a : Alg (ListF A) B)
  := Eval unfold tau_alg_ in MkMorph (tau_alg_morph ys a).

Lemma tau_fusion {A B} `{setoid C} (ys : list A)
  (a : Alg (ListF A) B) (c : RCoalg (ListF A) C):
  hylo (tau_alg ys a) c =e hylo a l_out \o hylo (tau_alg ys l_in) c.
Proof.
  symmetry. apply hylo_fusion_l.
  Opaque hylo.
  intros [[|h] kx]. simpl.
  - replace (hylo a l_out (hylo l_in ilist_coalg ys)) with
      ((hylo a l_out \o hylo l_in ilist_coalg) ys) by reflexivity.
    rewrite (deforest l_out_in).
    reflexivity.
  - simpl. rewrite hylo_unr at 1. simpl.
    reflexivity.
  Transparent hylo.
Qed.

Definition append {A} (l : list A) := hylo (tau_alg l l_in) ilist_coalg.

Lemma tt_cons {A} (a : A) : valid (Cont:=ListF A)(s_cons a, tt).
Proof. simpl. reflexivity. Qed.
Definition len_alg {A} : App (ListF A) int ~> int.
|{ x : (App (ListF A) _) ~> (
           match x with
           | MkCont sx kx =>
               match sx as s return (Container.Pos s -> _) -> _ with
               | s_nil => fun _ => 0%uint63
               | s_cons _ => fun k => (1 + k (MkElem tt (@tt_cons _ _)))%uint63
               end kx
           end
         )
  }|.
Defined.

Definition length {A} := cata (@len_alg A).

Definition example1 {A B} (f : A ~> B) ys : Ext (length \o Lmap f \o append ys).
  calculate.
  unfold length, Lmap, append, everywhere.
  rewrite !hylo_cata, hylo_map_fusion.
  rewrite <- (tau_fusion _ _ ilist_coalg).
  simpl.
  reflexivity.
Defined.

(** Example 2 from shortcut fusion in calc form [length \o rev ] *)

(* Quadratic reverse *)
(* Definition rev_alg {A} : Alg (ListF A) (list A). *)
(*   |{ *)
(*     x ~> match x with *)
(*       | MkCont sx kx => *)
(*           match sx with *)
(*           | s_nil => fun _ => nil *)
(*           | s_cons h => fun k => hylo (app_sing h) ilist_coalg (k (MkElem tt eq_refl)) *)
(*           end kx *)
(*       end *)
(*   }|. *)


Module ToExtract.
  Definition ex1 := Eval unfold example1 in @example1.
End ToExtract.

From Coq Require Extraction ExtrOcamlBasic ExtrOCamlInt63.
Set Extraction TypeExpand.
Extraction Inline val.
Set Extraction Flag 2047.
Recursive Extraction ToExtract.
