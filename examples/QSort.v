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

Require List.
Require Import Coq.Numbers.Cyclic.Int63.Sint63.

Definition merge : App (TreeF unit int) (list int) ~> list int:=
  ltac:(|{ x ~> match a_out x with
             | leaf _ => nil
             | node h l r => List.app l (h :: r)
             end}|).

Open Scope sint63_scope.
Definition c_split : Coalg (TreeF unit int) (list int) :=
  ltac:(|{ x ~> match x with
             | nil => a_leaf tt
             | cons h t =>
                 let (l, r) := List.partition (fun x => x <=? h) t in
                 a_node h l r
             end}|).
Close Scope sint63_scope.

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


(* YAY! quicksort in Coq as a divide-and-conquer "finite" hylo :-) *)
(* UPDATE 12/09/2023 by DC: this used to be mergesort, and at some
 * point I simply changed the implementation ...
 *)
Definition qsort : Ext (cata merge \o rana tsplit).
  calculate.
  (* rewrite <- ana_rana. *)
  (* rewrite compA, cata_ccata. *)
  rewrite cata_ana_hylo.
  Opaque wf_lt. simpl. Transparent wf_lt.
  reflexivity.
Defined.

Open Scope sint63_scope.
Definition times_two : int ~> int.
  refine {| app:= fun x => 2 * x |}.
  intros ??->. reflexivity.
Defined.
Close Scope sint63_scope.

Definition qsort_times_two
  : Ext (cata merge \o everywhere (nt_shape (L:=unit) id times_two) \o rana tsplit).
  calculate.
  unfold everywhere.
  rewrite hylo_cata.
  rewrite hylo_ana.
  rewrite hylo_map_fusion.
  rewrite deforest; last (rewrite l_out_in; reflexivity).
  unfold natural, eta, merge, tsplit, hylo, times_two, natT, app, mk_wf_coalg.
  Opaque wf_lt mult. simpl. Transparent wf_lt.
  reflexivity.
Defined.

Module Tests.
  Import List.
  Definition test := (1 :: 7 :: 2 :: 8 :: 10 :: 8 :: 1 :: nil)%sint63.
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
Set Extraction Flag 2047.
Recursive Extraction qsort.
Recursive Extraction qsort_times_two.
