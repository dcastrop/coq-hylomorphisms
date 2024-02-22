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

Fixpoint splitL (x : list nat) (acc : list nat * list nat) :=
  match x with
  | nil => acc
  | cons x xs => splitL xs (snd acc, cons x (fst acc))
  end.

Definition c_split : Coalg (TreeF (list nat) unit) (list nat).
  refine {|
      app := fun x =>
               if List.length x <=? 1
               then a_leaf x
               else let (l, r) := splitL x (nil, nil) in
                    a_node tt l r
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
Extraction Inline Valid.

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

Extraction Inline fst.
Extraction Inline snd.

Extraction Inline merge.
Extraction Inline a_leaf.
Extraction Inline a_node.
Extraction Inline a_out.
Extraction Inline c_split.
Extraction Inline tsplit.
Set Extraction Flag 2047.
Recursive Extraction msort.
