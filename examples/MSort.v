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

Require Import Lia.
Require List.
(* Require Import Nat. *)
Require Import Coq.Numbers.Cyclic.Int63.Sint63.

Fixpoint mergeL l1 l2 {struct l1} :=
  let fix merge_aux l2 :=
    match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | cons a1 l1', cons a2 l2' =>
      if a1 <=? a2 then cons a1 (mergeL l1' l2) else cons a2 (merge_aux l2')
    end%sint63
  in merge_aux l2.

Definition merge : App (TreeF (list int) unit) (list int) ~> list int :=
  ltac:(|{ x ~>
             match a_out x with
             | node _ l r => mergeL l r
             | leaf e => e
             end
    }|).

Fixpoint splitL (x : list int) (accL accR : list int) :=
  match x with
  | nil => (accL, accR)
  | cons x xs => splitL xs accR (cons x accL)
  end.

Notation max := Nat.max.

Definition len_pair (p : list int * list int) : nat
  := max (length (fst p)) (length (snd p)).

Lemma splitL_len : forall x a1 a2,
    length (fst (splitL x a1 a2)) <= max (length a1) (length a2) + length x /\
      length (snd (splitL x a1 a2)) <= max (length a1) (length a2) + length x.
Proof.
  induction x as [|h t Ih]; intros a1 a2; unfold len_pair; simpl in *.
  - lia.
  - specialize (Ih a2 (cons h a1)). simpl in *. lia.
Qed.

Definition c_split : Coalg (TreeF (list int) unit) (list int) :=
  ltac:(|{ x ~> match x with
             | nil | cons _ nil => a_leaf x
             | _ => let (l, r) := splitL x nil nil in
                    a_node tt l r
             end
    }|).

(* Needs to be defined, otherwise msort does not reduce!
 * UPDATE 12/09/2023 by DC: what's the nonsense above???
 *)

Lemma split_fin : respects_relation c_split (@length int) lt.
Proof.
  intros [|h [|h' t]] p; simpl in *; try apply (dom_leaf _ p).
  revert p; rewrite (eta_pair (splitL _ _ _)). simpl; intros p.
  destruct (splitL_len t (h::nil) (h'::nil)) as [H1 H2]; simpl in *.
  destruct p as [[|] V]; rewrite PeanoNat.Nat.lt_succ_r; trivial.
Qed.

Definition tsplit : RCoalg (TreeF (list int) unit) (list int)
  := mk_wf_coalg wf_lt split_fin.


(* YAY! quicksort in Coq as a divide-and-conquer "finite" hylo :-) *)
(* UPDATE 12/09/2023 by DC: this used to be mergesort, and at some
 * point I simply changed the implementation ...
 *)
Definition msort : Ext (cata merge \o rana tsplit).
  calculate.
  rewrite cata_ana_hylo.
  Opaque wf_lt.
  simpl.
  Transparent wf_lt.
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
  Eval compute in msort largeTest.
End Tests.


From Coq Require Extraction ExtrOcamlBasic ExtrOCamlInt63.
Extract Inlined Constant Nat.leb => "(<=)".
Set Extraction TypeExpand.
Extraction Inline val.
Set Extraction Flag 2047.
Recursive Extraction msort.
