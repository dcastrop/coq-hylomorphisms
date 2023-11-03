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

Definition merge : Alg (TreeF nat) (list nat).
  refine {|
      app := fun (x : App (TreeF nat) (list nat)) =>
               match a_out x with
               | None => nil
               | Some (h, l, r) => Datatypes.app l (h :: r)
               end
    |}.
  intros x y ->. auto with ffix.
Defined.

Definition c_split : Coalg (TreeF nat) (list nat).
  refine {|
      app := fun x =>
               match x with
               | nil => a_leaf
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

Definition tsplit : RCoalg (TreeF nat) (list nat) := Rec split_fin.


(* YAY! quicksort in Coq as a divide-and-conquer "finite" hylo :-) *)
(* UPDATE 12/09/2023 by DC: this used to be mergesort, and at some
 * point I simply changed the implementation ...
 *)
Definition qsort : Ext (cata merge \o rana tsplit).
  calculate.
  (* rewrite <- ana_rana. *)
  (* rewrite compA, cata_ccata. *)
  rewrite cata_ana_hylo.
  reflexivity.
Defined.

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extract Inlined Constant Nat.leb => "(<=)".
Set Extraction TypeExpand.
(* Set Extraction Conservative Types. *)
Extraction Inline e_lbranch.
Extraction Inline e_rbranch.
Extraction Inline dom_leaf.
Extraction Inline projT1.
Extraction Inline projT2.
Extraction Inline comp.

Extraction Inline val.
Extraction Inline InDom.

Extraction Inline app.
Extraction Inline coalg.
Extraction Inline val.
Extraction Inline shape.
Extraction Inline cont.
Extraction Inline hylo.
Extraction Inline hylo_f__.
Extraction Inline hylo_def.
Extraction Inline cata.
Extraction Inline ccata.
Extraction Inline ccata_.
Extraction Inline ccata_f.
Extraction Inline ccata_f_.
Extraction Inline liftP.
Extraction Inline liftP_f_.
Extraction Inline ana.
Extraction Inline ana_f.
Extraction Inline ana_f_.
Extraction Inline ana_f_u.
Extraction Inline rana.
Extraction Inline hylo_f.
Extraction Inline hylo_f_.
Extraction Inline LFix_out.
Extraction Inline l_in.
Extraction Inline l_out.
Extraction Inline g_in.
Extraction Inline g_out.
Extraction Inline lg_in.
Extraction Inline lg_out.
Extraction Inline GFix_out.

Extraction Inline merge.
Extraction Inline a_leaf.
Extraction Inline a_node.
Extraction Inline a_out.
Extraction Inline c_split.
Extraction Inline tsplit.
Set Extraction Flag 2047.
Recursive Extraction qsort.
