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
           let (sx, kx) := x in
               match sx return (Container.Pos sx -> _) -> _ with
               | Leaf _ _ => fun _ => nil
               | Node _ h => fun k => List.app (k (posL h)) (h :: k (posR h))
               end kx
  )}|.
Defined.

Open Scope uint63_scope.
Definition c_split : Coalg (TreeF unit int) (list int) :=
  ltac:(|{ x ~> match x with
             | nil => a_leaf tt
             | cons h t =>
                 let (l, r) := List.partition (fun x => x <? h) t in
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

Section QSortOK.
Inductive Sorted {A : Type} (R : A -> A -> bool) : list A -> Prop :=
  | Sorted_nil : Sorted R nil
  | Sorted_cons {a} {v : list A} : All (R a) v -> Sorted R v -> Sorted R (a :: v).

  Definition Permutation {A : Type} (l r : list A) := forall x, In x l <-> In x r.

  Definition leb x y : bool := (x <=? y)%uint63.

  Lemma sorted_app p :
    forall l r,
      Sorted leb l -> Sorted leb r ->
      All (fun x => x <? p)%uint63 l -> All (fun x => negb (x <? p))%uint63 r ->
      Sorted leb (l ++ r).
  Proof.
    induction l as [|h t Ih]; simpl; auto.
    intros r Sh Sr A B. inversion_clear Sh as [|h' t' Aleb Sl].
    constructor.
    + intros x H. apply in_app_or in H. destruct H; auto.
      specialize (B _ H); simpl in *.
      specialize (A h (or_introl eq_refl)). simpl in A.
      clear H Sl Aleb Sr Ih. unfold leb. apply negb_lt_le in B.
      apply lt_le in A; apply (leb_trans A B).
    + apply Ih; auto. intros x e.
      apply (A _ (or_intror e)).
  Qed.


  Lemma hylo_ind `{eA : setoid A} `{eB : setoid B} `{F : Cont Sh Pp}
    (P : A -> B -> Prop)
    : forall (a : Alg F B) (c : RCoalg F A),
      (forall x (Ih : forall e, P (cont (c x) e) (hylo a c (cont (c x) e))), P x (hylo a c x)) ->
      forall x, P x (hylo a c x).
  Proof.
    intros a c H x. induction (recP c x) as [x _ Ih]. apply H, Ih.
  Qed.

  Lemma hylo_correct : forall (l : list int),
      Sorted leb (hylo merge tsplit l) /\ Permutation l (hylo merge tsplit l).
  Proof.
    Opaque hylo.
    intros l. apply hylo_ind. clear l. intros l Ih. rewrite hylo_unr; simpl.
    destruct l as [|h t]; simpl in *.
    + do ! constructor; auto with *.
    + rewrite partition_as_filter in *; simpl in *.
      pose proof (Ih (posL h)) as IhL; specialize (Ih (posR h)).
      rename Ih into IhR; simpl in *.
      destruct IhR as [IhSr IhPr]; destruct IhL as [IhSl IhPl].
      split.
      - apply (@sorted_app h).
        * exact IhSl.
        * constructor; try exact IhSr.
          intros x e. apply IhPr in e. rewrite filter_In in e.
          destruct e as [_ negb_lt]. apply negb_lt_le; trivial.
        * intros x e. apply IhPl in e. rewrite filter_In in e.
          destruct e as [_ lt]; trivial.
        * intros x e. destruct e as [xh | e]; [subst; apply negb_lt_x_x|].
          apply IhPr in e. rewrite filter_In in e.
          destruct e as [_ lt]; trivial.
      - intros x. split.
        * intros [xh | e]; [subst; apply In_middle|].
          apply in_or_app.
          destruct (ltbP x h) as [l | l]; rewrite <- ltb_spec in l.
          rewrite <- (IhPl x), filter_In; auto.
          apply Bool.eq_true_not_negb in l.
          right; right. rewrite <- (IhPr x), filter_In; auto.
        * intros H; apply in_app_or in H; destruct H  as [inL|[eqh|inR]].
          right. rewrite <- (IhPl x), filter_In in inL. destruct inL; trivial.
          subst. left; trivial.
          right. rewrite <- (IhPr x), filter_In in inR. destruct inR; trivial.
    Transparent hylo.
    Qed.
End QSortOK.
