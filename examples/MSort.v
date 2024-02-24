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

About app.
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
Lemma split_fin : forall x, RecF c_split x.
Proof.
Admitted.

Definition tsplit : RCoalg (TreeF (list nat) unit) (list nat) := Rec split_fin.


(* YAY! quicksort in Coq as a divide-and-conquer "finite" hylo :-) *)
(* UPDATE 12/09/2023 by DC: this used to be mergesort, and at some
 * point I simply changed the implementation ...
 *)
Definition msort : Ext (cata merge \o rana tsplit).
  calculate.
  (* rewrite <- ana_rana. *)
  (* rewrite compA, cata_ccata. *)
  rewrite cata_ana_hylo.
  simpl.
  reflexivity.
Defined.

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extract Inlined Constant Nat.leb => "(<=)".
Set Extraction TypeExpand.
Extraction Inline val.
Set Extraction Flag 2047.
Recursive Extraction msort.
