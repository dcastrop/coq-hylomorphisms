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

Require Import Examples.BTree.

Require List.
Require Import Nat.

Fixpoint mergeL l1 l2 {struct l1} :=
  let fix merge_aux l2 :=
    match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | cons a1 l1', cons a2 l2' =>
      if a1 <=? a2 then cons a1 (mergeL l1' l2) else cons a2 (merge_aux l2')
    end
  in merge_aux l2.

Definition merge : App (TreeF (list nat) unit) (list nat) ~> list nat.
  refine {|
      app := fun x =>
               match a_out x with
               | node _ l r => mergeL l r
               | leaf e => e
               end
    |}.
  intros x y ->. auto with ffix.
Defined.

Fixpoint splitL (x : list nat) (accL accR : list nat) :=
  match x with
  | nil => (accL, accR)
  | cons x xs => splitL xs accR (cons x accL)
  end.

Definition len_pair (p : list nat * list nat)
  := max (length (fst p)) (length (snd p)).

Lemma splitL_len : forall x a1 a2,
    len_pair (splitL x a1 a2) <= max (length a1) (length a2) + length x.
Proof.
  induction x as [|h t Ih]; intros a1 a2; unfold len_pair; simpl in *.
  - rewrite <- plus_n_O. apply le_n.
  - specialize (Ih a2 (cons h a1)). simpl in *.
    apply (PeanoNat.Nat.le_trans _ _ _ Ih). clear Ih.
    rewrite <- plus_n_Sm, <- plus_Sn_m, PeanoNat.Nat.succ_max_distr.
    rewrite <- PeanoNat.Nat.add_le_mono_r.
    rewrite PeanoNat.Nat.max_comm.
    apply PeanoNat.Nat.max_le_compat; [|apply le_S]; apply le_n.
Qed.
Lemma splitL_len1 : forall x a1 a2,
    length (fst (splitL x a1 a2)) <=  max (length a1) (length a2) + length x.
Proof.
  intros x a1 a2.
  set (He := splitL_len x a1 a2).
  unfold len_pair in He. rewrite PeanoNat.Nat.max_lub_iff in He.
  destruct He; trivial.
Qed.
Lemma splitL_len2 : forall x a1 a2,
    length (snd (splitL x a1 a2)) <=  max (length a1) (length a2) + length x.
Proof.
  intros x a1 a2.
  set (He := splitL_len x a1 a2).
  unfold len_pair in He. rewrite PeanoNat.Nat.max_lub_iff in He.
  destruct He; trivial.
Qed.

Definition c_split : Coalg (TreeF (list nat) unit) (list nat).
  refine {|
      app := fun x =>
               match x with
               | nil | cons _ nil => a_leaf x
               | _ => let (l, r) := splitL x nil nil in
                      a_node tt l r
               end
    |}.
  intros x y H. simpl in H. subst. reflexivity.
Defined.

  (* Needs to be defined, otherwise msort does not reduce!
   * UPDATE 12/09/2023 by DC: what's the nonsense above???
   *)

Lemma split_fin : respects_relation c_split (@length nat) lt.
Proof.
  intros [|h [|h' t]] p; simpl in *; try apply (dom_leaf _ p).
  revert p; rewrite (eta_pair (splitL _ _ _)). simpl; intros p.
  destruct p as [[|] V]; simpl; rewrite PeanoNat.Nat.lt_succ_r.
  * apply splitL_len1.
  * apply splitL_len2.
Qed.

Definition tsplit : RCoalg (TreeF (list nat) unit) (list nat)
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
  Definition test := 1 :: 7 :: 2 :: 8 :: 10 :: 8 :: 1 :: nil.
  Fixpoint cycle n :=
    match n with
    | 0 => test
    | S n => test ++ cycle n
    end.
  Definition largeTest := Eval compute in cycle 10.
  Eval compute in msort largeTest.
End Tests.


From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extract Inlined Constant Nat.leb => "(<=)".
Set Extraction TypeExpand.
Extraction Inline val.
Set Extraction Flag 2047.
Recursive Extraction msort.
