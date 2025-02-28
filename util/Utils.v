Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import PeanoNat.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Require Import List.

Coercion is_true b := b = true.

Lemma eta_pair {A B} (p : A * B) : p = (fst p, snd p).
Proof. destruct p; trivial. Qed.

Lemma wf_lt : well_founded lt.
Proof.
  cut (forall x y, y < x -> Acc lt y).
  - intros H x. apply (H (S x) x), PeanoNat.Nat.lt_succ_diag_r.
  - fix Ih 1. intros [|x] y LT.
    + destruct (PeanoNat.Nat.nlt_0_r _ LT).
    + constructor. intros y' LT'. apply (Ih x). Guarded.
      rewrite PeanoNat.Nat.lt_succ_r in LT.
      apply (PeanoNat.Nat.lt_le_trans _ _ _ LT' LT).
Defined.

Lemma negb_lt_le x h : negb (x <? h)%uint63 -> (h <=? x)%uint63.
Proof.
    destruct (ltbP x h) as [|B]; try discriminate.
    apply BinInt.Z.nlt_ge in B.
    rewrite <- leb_spec in B; trivial.
Qed.

Lemma negb_lt_x_x x : negb (x <? x)%uint63.
Proof. unfold is_true. destruct (ltbP x x) as [|B]; auto with *. Qed.

Lemma lt_le x h : (x <? h)%uint63 -> (x <=? h)%uint63.
Proof.
    destruct (ltbP x h) as [|B]; try discriminate.
    intros _. unfold is_true. rewrite leb_spec.
    apply BinInt.Z.lt_le_incl; trivial.
Qed.

Lemma leb_trans x h i : (x <=? h)%uint63 -> (h <=? i)%uint63 -> (x <=? i)%uint63.
Proof.
  intros E1 E2. unfold is_true in *. rewrite leb_spec in *.
  apply (BinInt.Z.le_trans _ _ _ E1 E2).
Qed.

Lemma In_middle A l (x : A) r : In x (l ++ x :: r).
Proof. apply in_or_app; auto with *. Qed.

Definition All {A : Type} (P : A -> Prop) (l : list A) : Prop :=
  forall x, In x l -> P x.
