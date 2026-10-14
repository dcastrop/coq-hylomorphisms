Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Utils.
Require Import Hylo.Equivalence.
Require Import Hylo.Morphism.
Require Import Hylo.Container.

From Stdlib Require Import List.

(** Finite containers: the valid positions of each shape are listed, in a
  * fixed order and without duplicates. Positions have an arbitrary type [P]
  * with a decidable equality ([peq]); nothing else is assumed about it.
  *
  * The container is derived from the list ([fin_cont]): a position is valid
  * when it occurs in the list of its shape ([fvalid]). Equivalent shapes list
  * the same positions, so folding over the children of a shape respects [=e].
  *)
Record FinCont Sh `{Esh : setoid Sh} P :=
  MkFinCont
    { peq : P -> P -> bool;
      peq_spec : forall x y, peq x y = true <-> x = y;
      positions : Sh -> list P;
      positions_nodup : forall s, NoDup (positions s);
      positions_proper : forall s1 s2, s1 =e s2 -> positions s1 = positions s2;
    }.
Arguments FinCont Sh {Esh} P.
Arguments MkFinCont {Sh Esh P} peq peq_spec positions positions_nodup positions_proper.
Arguments peq {Sh Esh P} f x y.
Arguments peq_spec {Sh Esh P} f x y.
Arguments positions {Sh Esh P} f s.
Arguments positions_nodup {Sh Esh P} f s.
Arguments positions_proper {Sh Esh P} f [s1 s2] _.

Section Container.
  Context `{Esh : setoid Sh} {P : Type} (F : FinCont Sh P).

  (** A position is valid when it occurs in the positions of its shape. *)
  Definition fvalid (x : Sh * P) : bool := existsb (peq F (snd x)) (positions F (fst x)).

  Lemma fvalid_iff (s : Sh) (p : P) : fvalid (s, p) = true <-> In p (positions F s).
  Proof.
    unfold fvalid; simpl. rewrite existsb_exists. split.
    - intros [q [Hq E]]. apply (peq_spec F) in E. subst. trivial.
    - intros Hp. exists p. split; trivial. apply (peq_spec F). reflexivity.
  Qed.

  Lemma positions_sound (s : Sh) (p : P) : In p (positions F s) -> fvalid (s, p) = true.
  Proof. apply fvalid_iff. Qed.

  Lemma positions_complete (s : Sh) (p : P) : fvalid (s, p) = true -> In p (positions F s).
  Proof. apply fvalid_iff. Qed.

  Lemma fin_valid_morph
    : forall x y : Sh * P, x =e y -> fvalid x =e fvalid y.
  Proof.
    intros [s1 p1] [s2 p2] [Es Ep]; simpl in *; subst p2.
    destruct (fvalid (s1, p1)) eqn:V1, (fvalid (s2, p1)) eqn:V2; trivial.
    - apply fvalid_iff in V1. rewrite (positions_proper F Es) in V1.
      apply fvalid_iff in V1. congruence.
    - apply fvalid_iff in V2. rewrite <- (positions_proper F Es) in V2.
      apply fvalid_iff in V2. congruence.
  Qed.

  Definition fin_valid : Sh * P ~> bool := MkMorph fin_valid_morph.

  (** The container of a finite container. *)
  Definition fin_cont : Cont Sh P := {| valid := fin_valid |}.
End Container.
Arguments fvalid {Sh Esh P} F x.
Arguments fvalid_iff {Sh Esh P} F s p.
Arguments positions_sound {Sh Esh P} F s p _.
Arguments positions_complete {Sh Esh P} F s p _.

Section Elems.
  Context `{Esh : setoid Sh} {P : Type} (F : FinCont Sh P).

  Lemma positions_valid (s : Sh) (p : P)
    : In p (positions F s) -> valid (F:=fin_cont F) (s, p).
  Proof. intros Hp. apply (positions_sound F s p Hp). Qed.

  Fixpoint elems_ (s : Sh) (l : list P)
    : (forall p, In p l -> valid (F:=fin_cont F) (s, p)) -> list (Pos (F:=fin_cont F) s) :=
    match l with
    | nil => fun _ => nil
    | p :: l =>
        fun H => @MkElem Sh Esh P (fin_cont F) s p (H p (or_introl eq_refl))
                   :: @elems_ s l (fun q Hq => H q (or_intror Hq))
    end.

  (** The positions of a shape, as elements of [Pos s]. *)
  Definition elems (s : Sh) : list (Pos (F:=fin_cont F) s) :=
    @elems_ s (positions F s) (@positions_valid s).

  Lemma elems_val_ (s : Sh) (l : list P) H : map val (@elems_ s l H) = l.
  Proof.
    induction l as [|p l Ih]; simpl; trivial.
    rewrite Ih. reflexivity.
  Qed.

  Lemma elems_val (s : Sh) : map val (elems s) = positions F s.
  Proof. apply elems_val_. Qed.

  Lemma elems_complete (s : Sh) (e : Pos (F:=fin_cont F) s) : In e (elems s).
  Proof.
    assert (Hin : In (val e) (map val (elems s))).
    { rewrite elems_val. apply (positions_complete F s (val e)).
      change (is_true (valid (F:=fin_cont F) (s, val e))). exact (Valid e). }
    apply in_map_iff in Hin. destruct Hin as [e' [Hv Hin]].
    rewrite <- (elem_val_eq Hv). trivial.
  Qed.

  Lemma elems_NoDup (s : Sh) : NoDup (elems s).
  Proof.
    apply (NoDup_map_inv val). rewrite elems_val. apply positions_nodup.
  Qed.
End Elems.
