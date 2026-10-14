Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Utils.
Require Import Hylo.Equivalence.
Require Import Hylo.Morphism.
Require Import Hylo.Container.

From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

(** Finite containers: each shape has an arity, and its positions are the
  * natural numbers below it. The container is derived from the arity
  * ([fin_cont]), so its positions are listed in a fixed order and without
  * duplicates ([elems]).
  *)
Record FinCont Sh `{Esh : setoid Sh} :=
  MkFinCont
    { arity : Sh -> nat;
      arity_proper : forall s1 s2, s1 =e s2 -> arity s1 = arity s2;
    }.
Arguments FinCont Sh {_}.
Arguments MkFinCont {Sh _} arity arity_proper.

Section Container.
  Context `{Esh : setoid Sh} (F : FinCont Sh).

  Definition fin_valid_ (x : Sh * nat) : bool := snd x <? arity F (fst x).

  Lemma fin_valid_morph : forall x y, x =e y -> fin_valid_ x =e fin_valid_ y.
  Proof.
    intros [s1 i1] [s2 i2] [Es Ei]; simpl in *. unfold fin_valid_; simpl.
    rewrite (arity_proper F Es), Ei. reflexivity.
  Qed.

  Definition fin_valid : Sh * nat ~> bool := MkMorph fin_valid_morph.

  (** The container of a finite container. *)
  Definition fin_cont : Cont Sh nat := {| valid := fin_valid |}.

  Lemma fin_valid_lt (s : Sh) (i : nat)
    : valid (F:=fin_cont) (s, i) <-> i < arity F s.
  Proof. simpl. unfold fin_valid_, is_true; simpl. apply Nat.ltb_lt. Qed.
End Container.

Section Elems.
  Context `{Esh : setoid Sh} (F : FinCont Sh).

  Lemma elems_valid (s : Sh) (i m : nat)
    : i + S m <= arity F s -> valid (F:=fin_cont F) (s, i).
  Proof. intros B. apply fin_valid_lt. lia. Qed.

  Lemma elems_next (s : Sh) (i m : nat)
    : i + S m <= arity F s -> S i + m <= arity F s.
  Proof. lia. Qed.

  Fixpoint elems_ (s : Sh) (i n : nat)
    : i + n <= arity F s -> list (Pos (F:=fin_cont F) s) :=
    match n with
    | 0 => fun _ => nil
    | S m => fun B => MkElem i (elems_valid B) :: @elems_ s (S i) m (elems_next B)
    end.

  (** The positions of a shape, [0 .. arity s - 1], as elements of [Pos s]. *)
  Definition elems (s : Sh) : list (Pos (F:=fin_cont F) s) :=
    @elems_ s 0 (arity F s) (le_n _).

  Lemma elems_val_ (s : Sh) (i n : nat) B
    : map val (@elems_ s i n B) = seq i n.
  Proof.
    revert i B. induction n as [|n Ih]; intros i B; simpl; trivial.
    rewrite Ih. reflexivity.
  Qed.

  Lemma elems_val (s : Sh) : map val (elems s) = seq 0 (arity F s).
  Proof. apply elems_val_. Qed.

  Lemma elems_complete (s : Sh) (e : Pos (F:=fin_cont F) s) : In e (elems s).
  Proof.
    assert (Hin : In (val e) (map val (elems s))).
    { rewrite elems_val. apply in_seq. split; [lia|].
      apply fin_valid_lt, Valid. }
    apply in_map_iff in Hin. destruct Hin as [e' [Hv Hin]].
    rewrite <- (elem_val_eq Hv). trivial.
  Qed.

  Lemma elems_NoDup (s : Sh) : NoDup (elems s).
  Proof.
    apply (NoDup_map_inv val). rewrite elems_val. apply seq_NoDup.
  Qed.
End Elems.
