Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import HYLO.Equivalence.
Require Import HYLO.Morphism.
Require Import HYLO.Container.
Require Import HYLO.Algebra.
Require Import HYLO.Coalgebra.

Section FCoalgDef.
  Context `(F : Container Sh P).

  Inductive RecF `{equiv A} (h : Coalg F A) : A -> Prop :=
  | RecF_fold x : (forall e, RecF h (cont (h x) e)) -> RecF h x.

  Lemma RecF_inv `{eA : equiv A} (h : Coalg F A) x
    : RecF h x -> forall e, RecF h (cont (h x) e).
  Proof. intros []. auto. Defined.

  Lemma ext_eq_fin `(eA : equiv A) (c0 c1 : A ~> App F A) (H : c0 =e c1)
    (x y : A) (H0 : x =e y) : RecF c0 x -> RecF c1 y.
  Proof.
    intros f. revert c1 y H H0. induction f as [x H' Ih]. intros c1 y H H0.
    constructor. intros e.
    assert (Exy : c0 x =e c1 y) by (rewrite H, H0; reflexivity).
    simpl in Exy. destruct Exy as [Sxy Kxy].
    symmetry in Sxy. destruct (elem_dom_irr Sxy e) as [e' Hv].
    apply (Ih e'); trivial. apply Kxy. symmetry. trivial.
  Qed.

  Add Parametric Morphism `{eA : equiv A} : (@RecF A eA)
      with signature
      (eqRel (A:=Coalg F A))
        ==> (eqRel (A:=A))
        ==> (eqRel (A:=Prop))
        as finMorphism.
  Proof.
    intros. simpl. split; apply ext_eq_fin; trivial; symmetry; trivial.
  Qed.

  Definition Rec `{eA : equiv A} (c : Coalg F A) := forall x, RecF c x.
  Definition RCoalg `{eA : equiv A} := sig Rec.
  Arguments RCoalg A {eA}.

  Coercion coalg `{equiv A} : RCoalg A -> A ~> App F A := @proj1_sig _ _.

  Definition terminating `{equiv A} :
    forall (h : RCoalg A) x, RecF h x := @proj2_sig _ _.

  #[export] Instance equiv_rcoalg `{equiv A} : equiv (RCoalg A).
  Proof with auto with ffix.
    refine {|
        eqRel := fun x y => coalg x =e coalg y
      |}...
    intros x y z H1 H2. transitivity y...
  Defined.

  (* Finite Trees *)
  Inductive FinF : GFix F -> Prop :=
  | FinF_fold (x : GFix F) : (forall e, FinF (cont (GFix_out x) e)) -> FinF x.

  Lemma ana_rcoalg_fin `{equiv A} (c : Coalg F A) (Rc : Rec c)
    : forall x, FinF (ana c x).
  Proof.
    simpl. intros x. generalize (Rc x).
    intros Rcx. induction Rcx as [x _ Ih]. constructor. rewrite unfold_ana_f.
    simpl. exact Ih.
  Qed.

  Lemma fin_ana_rcoalg `{equiv A}
    (h : Coalg F A) (FT : forall x, FinF (ana h x)) : Rec h.
  Proof.
    intros x. specialize (FT x). revert FT.
    generalize (eq_refl (ana h x)). generalize (ana h x) at -1. intros g Eg HF.
    revert x Eg. induction HF as [g _ Ih]. intros x Eg. subst. simpl in *.
    rewrite unfold_ana_f in *. simpl in *. constructor. intros e.
    specialize (Ih e _ eq_refl). trivial.
  Qed.

  Corollary ana_rec_term `{equiv A} (h : Coalg F A)
    : (forall x, FinF (ana h x)) <-> Rec h.
  Proof. split; try apply ana_rcoalg_fin; apply fin_ana_rcoalg. Qed.

  Notation rana_f__ h :=
    (fix f x H :=
      let hx := h x in
      LFix_in (MkCont (shape hx) (fun e => f (cont hx e) (RecF_inv H e)))).

  Lemma rana_f_irr `{eA : equiv A} (h : Coalg F A)
    : forall (x : A) (F1 F2 : RecF h x), rana_f__ h x F1 =e rana_f__ h x F2.
  Proof.
    simpl. fix Ih 2. intros x0 [x Fx] F2. clear x0. destruct F2 as [x Fy].
    simpl. split; [reflexivity| intros e1 e2 d]. rewrite (elem_val_eq d).
    apply Ih. Guarded.
  Qed.

  Notation rana_f_ h x := (rana_f__ h x (terminating h x)).

  Lemma rana_f_arr `{eA : equiv A} (h : RCoalg A)
    : forall x y, x =e y -> rana_f_ h x =e rana_f_ h y.
  Proof.
    intros x y.
    generalize (terminating h x) (terminating h y). revert x y.
    fix Ih 3. intros x y [x' Fx] [y' Fy] Hxy. simpl in *. split.
    - destruct (app_eq h Hxy). auto.
    - intros e d1 d2. simpl. apply Ih. Guarded.
    destruct (app_eq h Hxy). auto.
  Qed.

  Notation rana_f h := (MkMorph (rana_f_arr h)).

  Lemma rana_arr `{eA : equiv A}
    : forall x y : RCoalg A, x =e y -> rana_f x =e rana_f y.
  Proof.
    intros f g Efg x. simpl.
    generalize (terminating f x) (terminating g x). intros Fx.
    generalize (e_refl x). generalize x at 2 3 5. intros y Ey Fy.
    revert x Fx y Fy Ey.
    fix Ih 2.
    intros x' [x Fx]. clear x'.
    intros y' [y Fy]. clear y'.
    intros Exy. simpl.
    assert (He : f x =e g y) by (rewrite Exy; apply Efg).
    destruct He as [Sxy Kxy]. split; trivial.
    intros e1 e2 Hv. apply Ih. Guarded.
    apply Kxy. trivial.
  Qed.

  Definition rana `{eA : equiv A} : RCoalg A ~> A ~> LFix F
    := MkMorph rana_arr.

  Lemma LFixR_fold (x y : LFix F) : LFixR x y = (x =e y).
  Proof. auto. Qed.

  Lemma rana_univ_r A (eA : equiv A) (h : RCoalg A) (f : A ~> LFix F)
    : f =e l_in \o fmap f \o h -> f =e rana h.
  Proof.
    intros H. unfold rana. simpl. intros x. generalize (terminating h x).
    revert x.  fix Ih 2. intros x0 [x Fx]. clear x0.
    rewrite LFixR_fold, (H _). simpl.
    split; [reflexivity| intros d1 d2 e]. rewrite (elem_val_eq e). apply Ih.
  Qed.

  Lemma rana_univ_l A {eA : equiv A} (h : RCoalg A) (f : A ~> LFix F)
    : f =e rana h -> f =e l_in \o fmap f \o h.
  Proof.
    intros H x0. rewrite (H _). simpl. unfold rana.
    generalize (terminating h x0) as Fx. intros [x Fx]. clear x0. simpl.
    split; [reflexivity| intros d1 d2 e]. rewrite (elem_val_eq e).
    generalize (H (cont (coalg h x) d2)). simpl. rewrite !LFixR_fold.
    intros Hrw. rewrite Hrw. apply rana_f_irr.
  Qed.

  Lemma rana_univ A {eA : equiv A} (h : RCoalg A) (f : A ~> LFix F)
    : f =e rana h <-> f =e l_in \o fmap f \o h.
  Proof. split;[apply rana_univ_l|apply rana_univ_r]. Qed.
End FCoalgDef.
Arguments RCoalg {Sh Esh P} F A {eA}.

Arguments rana & {Sh}%type_scope {Esh} {P}%type_scope {F} {A}%type_scope {eA}.
