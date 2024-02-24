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

Definition merge : App (TreeF unit nat) (list nat) ~> list nat.
  refine {|
      app := fun x =>
               match a_out x with
               | leaf _ => nil
               | node h l r => Datatypes.app l (h :: r)
               end
    |}.
  intros x y ->. auto with ffix.
Defined.

Definition c_split : Coalg (TreeF unit nat) (list nat).
  refine {|
      app := fun x =>
               match x with
               | nil => a_leaf tt
               | cons h t =>
                   let l := List.filter (fun x => Nat.leb x h) t in
                   let r := List.filter (fun x => negb (Nat.leb x h)) t in
                   a_node h l r
               end
    |}.
  intros x y ->. auto with ffix.
Defined.

  (* Needs to be defined, otherwise qsort does not reduce!
   * UPDATE 12/09/2023 by DC: what's the nonsense above???
   *)
Lemma split_fin : forall x, RecF c_split x.
Proof.
  intros x. generalize (PeanoNat.Nat.leb_refl (List.length x)).
  generalize (length x) at 2. intros n. revert x.
  induction n as [|n Ih]; intros [|h t] H; simpl in *; try discriminate;
    constructor; intros e; try destruct (dom_leaf_false e).
  destruct e as [se ke].
  destruct se; simpl in *; apply Ih, length_filter, H.
Qed.

Definition tsplit : RCoalg (TreeF unit nat) (list nat) := Rec split_fin.


(* YAY! quicksort in Coq as a divide-and-conquer "finite" hylo :-) *)
(* UPDATE 12/09/2023 by DC: this used to be mergesort, and at some
 * point I simply changed the implementation ...
 *)
Definition qsort : Ext (cata merge \o rana tsplit).
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
Recursive Extraction qsort.
