Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import PeanoNat.

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
