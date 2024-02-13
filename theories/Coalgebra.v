Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Paco.paco.
Require Import Util.Cofix.

Require Import HYLO.Equivalence.
Require Import HYLO.Morphism.
Require Import HYLO.Container.

Notation Coalg F A := (A ~> App F A) (only parsing).

Section CoalgDef.
  Context `(F : Cont Sh P).

  Set Primitive Projections.
  CoInductive GFix : Type := GFix_in { GFix_out : App F GFix }.
  Unset Primitive Projections.

  Notation gshape x := (shape (GFix_out x)).
  Notation gcont x := (cont (GFix_out x)).
  Notation grelT := (GFix -> GFix -> Prop) (only parsing).

  Inductive GFixR_ (G : grelT) (x y : GFix) : Prop :=
  | GFixR_in_
      (ShE : gshape x =e gshape y)
      (ElemE : forall e1 e2, val e1 = val e2 -> G (gcont x e1) (gcont y e2)).

  Definition GFixR : grelT := paco2 GFixR_ bot2.

  Lemma GFixR_in (x y : GFix) (ShE : gshape x =e gshape y)
    (ElemE : forall e1 e2, val e1 = val e2 -> GFixR (gcont x e1) (gcont y e2))
    : GFixR x y.
  Proof.
    apply paco2_fold. constructor; trivial.
    intros e1 e2 Heq; left. apply ElemE. trivial.
  Qed.
  Hint Resolve GFixR_in : ffix.

  Lemma GFixR_mon : monotone2 GFixR_.
  Proof.
    intros x y r rr [sh k] H.
    apply (GFixR_in_ sh).
    intros e1 e2 Ev. apply H, k, Ev.
  Qed.
  Hint Resolve GFixR_mon : gfix.

  Lemma GFixR_unfold x y (R : GFixR x y)
    : (gshape x =e gshape y) /\
        (forall e1 e2, val e1 = val e2 -> GFixR (gcont x e1) (gcont y e2)).
  Proof.
    apply paco2_unfold in R; auto with gfix. destruct R as [SE KE].
    split; trivial. intros e1 e2 Hv. destruct (KE e1 e2 Hv) as [|[]]. trivial.
  Qed.

  Lemma GFixR_refl : forall x, GFixR x x.
  Proof.
    intro x. coind CH. intros x.
    apply paco2_fold. constructor.
    - reflexivity.
    - intros e1 e2 Ev. right. rewrite (cont_valid_irrelevant Ev). apply CH.
  Qed.

  Lemma GFixR_sym : forall x y, GFixR x y -> GFixR y x.
  Proof.
    intros x y. coind CH. intros x y Gf.
    apply paco2_unfold in Gf; eauto with gfix.
    destruct Gf as [Hsh Hk]. apply e_sym in Hsh.
    apply paco2_fold. apply (GFixR_in_ Hsh).
    intros e1 e2 Hv. right. apply CH.
    symmetry in Hv. specialize (Hk e2 e1 Hv). destruct Hk as [Hk|Hk].
    - apply Hk.
    - destruct Hk.
  Qed.

  Lemma GFixR_trans : forall x y z, GFixR x y -> GFixR y z -> GFixR x z.
  Proof.
    intros x y z. revert y. coind CH. intros x z y Hxy Hyz.
    apply paco2_unfold in Hxy, Hyz; eauto with gfix.
    destruct Hxy as [HxyS HxyK]. destruct Hyz as [HyzS HyzK].
    apply paco2_fold.
    assert (HxzS : gshape x =e gshape z) by (rewrite HxyS; trivial).
    apply (GFixR_in_ HxzS). intros ex ez Veq. right.
    destruct (elem_valid_irr HxyS ex) as [ey Veq2].
    assert (Veq3 : val ey = val ez) by (rewrite <- Veq2; trivial).
    apply (CH (gcont x ex) (gcont z  ez) (gcont y ey)).
    - destruct (HxyK ex ey Veq2) as [Gf|[]]. trivial.
    - destruct (HyzK ey ez Veq3) as [Gf|[]]. trivial.
  Qed.

  #[export] Instance GFix_Eq : equiv GFix :=
    {| eqRel := GFixR;
      e_refl := GFixR_refl;
      e_sym := GFixR_sym;
      e_trans := GFixR_trans;
    |}.

  Lemma l_in_eq (x y : App F GFix) : x =e y -> GFix_in x =e  GFix_in y.
  Proof. simpl. intros []; auto with ffix. Qed.

  Lemma g_out_eq (x y : GFix) : x =e y -> GFix_out x  =e GFix_out y.
  Proof.
    simpl. intros Gf. apply paco2_unfold in Gf; auto with gfix.
    destruct Gf as [ShE ElemE]. constructor; trivial.
    intros e1 e2 Veq. destruct (ElemE e1 e2 Veq) as [Gf|[]]. trivial.
  Qed.

  Notation Alg F A := (App F A ~> A) (only parsing).

  Definition g_in : Alg F GFix := MkMorph l_in_eq.
  Definition g_out : Coalg F GFix := MkMorph g_out_eq.

  Lemma g_in_out : g_in \o g_out =e id (A:=GFix).
  Proof.
    intros x. simpl.
    apply paco2_fold. constructor; auto with ffix.
    intros e1 e2 Ev. simpl in *. left.
    rewrite (elem_val_eq Ev). apply GFixR_refl.
  Qed.

  Lemma g_out_in : g_out \o g_in =e id (A:=App F GFix).
  Proof. simpl. intros. generalize (e_refl x). simpl. trivial. Qed.

  Definition ana_f_u `{equiv A} (c : Coalg F A) (gf : A -> GFix) (x : A) :=
    let cx := c x in MkCont (shape cx) (fun e => gf (cont cx e)).

  Definition ana_f_ `{equiv A} (c : Coalg F A)
    := cofix f x := GFix_in (ana_f_u c f x).

  Lemma unfold_ana_f `{equiv A} (c : Coalg F A) x
    : GFix_out (ana_f_ c x) = ana_f_u c (ana_f_ c) x.
  Proof. reflexivity. Qed.

  Lemma ana_f_arr `{eA : equiv A} (c : Coalg F A)
    : forall x y, x =e y -> ana_f_ c x =e ana_f_ c y.
  Proof.
    coind CH. intros x y Exy.
    apply paco2_fold.
    assert (Rxy : c x =e c y) by (rewrite Exy; reflexivity).
    simpl in Rxy. destruct Rxy as [Es Ek].
    constructor; trivial. do 2 rewrite unfold_ana_f. simpl.
    intros e1 e2 Hv. right. apply CH.
    apply Ek; trivial.
  Qed.

  Definition ana_f `(eA : equiv A) (c : Coalg F A) : A ~> GFix
    := MkMorph (ana_f_arr c).

  Lemma ana_arr `{eA : equiv A}
    : forall x y : Coalg F A, x =e y -> ana_f x =e ana_f y.
  Proof.
    intros f g Hfg x. generalize (e_refl x). generalize x at 2 4. intros y Hxy.
    revert f g Hfg x y Hxy. coind CH. intros f g He x y Hxy.
    assert (Rfg : f x =e g y) by (rewrite Hxy; apply He).
    simpl in Rfg. destruct Rfg as [Es Ek].
    apply paco2_fold. constructor; trivial.
    intros e1 e2 Hv. right. apply CH; trivial.
    apply Ek. trivial.
  Qed.

  Definition ana `{eA : equiv A} : Coalg F A ~> A ~> GFix := MkMorph ana_arr.

  Lemma ana_univ_r `(eA : equiv A) (h : Coalg F A) (f : A ~> GFix)
    : f =e g_in \o fmap f \o h -> f =e ana h.
  Proof.
    intros He x. simpl.
    generalize (e_refl (f x)). generalize (f x) at 1 3. revert x.
    coind CH. intros g0 x Ef.
    assert (Rfg : g0 =e g_in (fmap f (h x))) by (rewrite Ef; apply He).

    apply paco2_unfold in Rfg; auto with gfix. destruct Rfg as [Es Ek].
    simpl in Es, Ek.

    apply paco2_fold. constructor; trivial.
    intros e1 e2 Hv. right. apply CH.
    specialize (Ek e1 e2 Hv). destruct Ek as [|[]]. trivial.
  Qed.

  Lemma ana_univ_l `{eA : equiv A} (h : Coalg F A) (f : A ~> GFix)
    : f =e ana h -> f =e g_in \o fmap f \o h.
  Proof.
    intros H. rewrite H. intros x. simpl.
    apply paco2_fold. constructor; simpl; try reflexivity.
    rewrite unfold_ana_f. simpl. intros e1 e2 Hv.
    rewrite (elem_val_eq Hv). left. apply GFixR_refl.
  Qed.

  Lemma ana_univ `{eA : equiv A} (h : Coalg F A) (f : A ~> GFix)
    : f =e ana h <-> f =e g_in \o fmap f \o h.
  Proof. split;[apply ana_univ_l|apply ana_univ_r]. Qed.

  Corollary ana_unfold `{eA : equiv A} (h : Coalg F A) :
    ana h =e g_in \o fmap (ana h) \o h.
  Proof. rewrite <- ana_univ. reflexivity. Qed.
End CoalgDef.

Arguments ana {Sh}%type_scope {Esh} {P}%type_scope {F} {A}%type_scope {eA}.
Arguments g_in & {Sh}%type_scope {Esh} {P}%type_scope {F}.
Arguments g_out & {Sh}%type_scope {Esh} {P}%type_scope {F}.
