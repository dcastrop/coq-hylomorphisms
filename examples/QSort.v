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

Require Import List.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.

Definition merge : App (TreeF unit int) (list int) ~> list int.
|{ x : (App (TreeF unit int) (list int)) ~> (
           match x with
           | MkCont sx kx =>
               match sx return (Container.Pos sx -> _) -> _ with
               | Leaf _ _ => fun _ => nil
               | Node _ h => fun k => List.app (k (posL h)) (h :: k (posR h))
               end kx
           end
  )}|.
Defined.

Open Scope uint63_scope.
Definition c_split : Coalg (TreeF unit int) (list int) :=
  ltac:(|{ x ~> match x with
             | nil => a_leaf tt
             | cons h t =>
                 let (l, r) := List.partition (fun x => x <=? h) t in
                 a_node h l r
             end}|).
Close Scope uint63_scope.

(* Needs to be defined, otherwise qsort does not reduce!
 * UPDATE 12/09/2023: what's the nonsense above???
 * UPDATE 25/02/2024: AAH! nope, the *termination* proof needs to be defined
 * if we want to do Eval compute and the like (otherwise the fixpoint will
  * never reduce)
 *)
Lemma split_fin : respects_relation c_split (@length int) lt.
Proof.
  intros [|h t] p; simpl in *; try (apply (dom_leaf _ p)).
  rewrite PeanoNat.Nat.lt_succ_r. revert p. rewrite List.partition_as_filter.
  intros []; simpl in *. destruct val; apply List.filter_length_le.
Qed.

Definition tsplit : RCoalg (TreeF unit int) (list int)
  := mk_wf_coalg wf_lt split_fin.

Definition Lmap {A B} (f : A ~> B) : list A ~> list B.
|{ x ~> (List.map f x) }|.
Defined.

Ltac eq_args :=
  repeat (f_equal; auto with ffix; try apply bool_irrelevance).

Lemma Lmap_merge (f : int ~> int)
  : Lmap f \o merge =e merge \o natural (nt_shape id f) \o fmap (Lmap f).
Proof.
  intros [[n|n] kx]; simpl in *; auto with *.
  rewrite map_app; simpl. unfold posL, posR.
  eq_args.
Qed.

Definition qsort : Ext (cata merge \o rana tsplit).
  calculate.
  (* rewrite <- ana_rana. *)
  (* rewrite compA, cata_ccata. *)
  rewrite cata_ana_hylo.
  Opaque wf_lt. simpl. Transparent wf_lt.
  reflexivity.
Defined.

Open Scope uint63_scope.
Definition times_two : int ~> int.
|{ x ~> (2 * x) }|.
Defined.
Close Scope uint63_scope.

Definition qsort_times_two
  : Ext (Lmap times_two \o cata merge \o rana tsplit).
  calculate.
  assert (RW1 : Lmap times_two \o cata merge
                =e hylo (merge \o natural (nt_shape id times_two)) l_out).
  {
    apply hylo_univ.
    rewrite fmap_comp, <- !compA. rewrite compA, compA.
    rewrite <- Lmap_merge, <- !compA, (compA merge), <- cata_unfold.
    reflexivity.
  }
  rewrite RW1, hylo_ana, deforest.
  2:{ apply l_out_in. }
  Opaque wf_lt. simpl. Transparent wf_lt.
  reflexivity.
Defined.

Module Tests.
  Import List.
  Definition test := (1 :: 7 :: 2 :: 8 :: 10 :: 8 :: 1 :: nil)%uint63.
  Fixpoint cycle n :=
    match n with
    | 0 => test
    | S n => test ++ cycle n
    end.
  Definition largeTest := Eval compute in cycle 10.
  Eval compute in qsort largeTest.
  Eval compute in qsort_times_two largeTest.
End Tests.

From Coq Require Extraction ExtrOcamlBasic ExtrOCamlInt63.
Set Extraction TypeExpand.
Extraction Inline val.
Extraction Inline posL.
Extraction Inline posR.
Set Extraction Flag 2047.
Recursive Extraction qsort.
Recursive Extraction qsort_times_two.
