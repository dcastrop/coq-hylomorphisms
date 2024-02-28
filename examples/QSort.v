Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import HYLO.Equivalence.
Import StdEquiv.
Require Import HYLO.Morphism.
Require Import HYLO.Container.
Require Import HYLO.Algebra.
Require Import HYLO.Coalgebra.
Require Import HYLO.FCoalgebra.
Require Import HYLO.Hylo.

Require Import Examples.BTree.

Require List.

Definition merge : App (TreeF unit nat) (list nat) ~> list nat :=
  ltac:(|{ x ~>
               match a_out x with
               | leaf _ => nil
               | node h l r => Datatypes.app l (h :: r)
               end
    }|).

Definition c_split : Coalg (TreeF unit nat) (list nat) :=
  ltac:(|{ x ~>
             match x with
             | nil => a_leaf tt
             | cons h t =>
                 let (l, r) := List.partition (fun x => Nat.leb x h) t in
                 a_node h l r
             end
    }|).

(* Needs to be defined, otherwise qsort does not reduce!
 * UPDATE 12/09/2023: what's the nonsense above???
 * UPDATE 25/02/2024: AAH! nope, the *termination* proof needs to be defined
 * if we want to do Eval compute and the like (otherwise the fixpoint will
  * never reduce)
 *)
Lemma split_fin : respects_relation c_split (@length nat) lt.
Proof.
  intros [|h t] p; simpl in *; try (apply (dom_leaf _ p)).
  rewrite PeanoNat.Nat.lt_succ_r. destruct (val p); apply length_filter.
Qed.

Definition tsplit : RCoalg (TreeF unit nat) (list nat)
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

Module Tests.
  Import List.
  Definition test := 1 :: 7 :: 2 :: 8 :: 10 :: 8 :: 1 :: nil.
  Fixpoint cycle n :=
    match n with
    | 0 => test
    | S n => test ++ cycle n
    end.
  Definition largeTest := Eval compute in cycle 10.
  Eval compute in qsort largeTest.
End Tests.

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extract Inlined Constant Nat.leb => "(<=)".
Set Extraction TypeExpand.
Extraction Inline val.
Set Extraction Flag 2047.
Recursive Extraction qsort.
