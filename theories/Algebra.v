Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import HYLO.Equivalence.
Require Import HYLO.Morphism.
Require Import HYLO.Container.

Notation Alg F A := (App F A ~> A).

Section AlgDef.
  Context `(F : Container Sh Po).

  Unset Elimination Schemes.

  Inductive LFix  : Type := LFix_in { LFix_out : App F LFix }.

  Set Elimination Schemes.

  Lemma LFix_rect [P : LFix -> Type]
    : (forall x : App F LFix,
          (forall e : Pos (shape x), P (cont x e)) ->
          P (LFix_in x))
      -> forall l : LFix, P l.
  Proof.
    intros H. fix Ih 1. intros []. apply H. intros e. apply Ih. Guarded.
  Defined.
  Lemma LFix_rec [P : LFix -> Set]
    : (forall x : App F LFix,
          (forall e : Pos (shape x), P (cont x e)) ->
          P (LFix_in x))
      -> forall l : LFix, P l.
  Proof. intros H. apply LFix_rect, H. Defined.
  Lemma LFix_ind [P : LFix -> Prop]
    : (forall x : App F LFix,
          (forall e : Pos (shape x), P (cont x e)) ->
          P (LFix_in x))
      -> forall l : LFix, P l.
  Proof. intros H. apply LFix_rect, H. Defined.

  Fixpoint LFixR (x y : LFix) : Prop :=
    let f_x := LFix_out x in
    let f_y := LFix_out y in
    shape f_x =e shape f_y /\
      (forall e1 e2, val e1 = val e2 -> LFixR (cont f_x e1) (cont f_y e2)).

  Lemma LFixR_refl (x : LFix) : LFixR x x.
  Proof.
    induction x as [x Ih]. simpl. split; try reflexivity.
    intros e1 e2 Heq. rewrite (elem_val_eq Heq). apply Ih.
  Qed.

  Lemma LFixR_sym (x y : LFix) : LFixR x y -> LFixR y x.
  Proof.
    revert y. induction x as [x Ih].
    intros [y] [Sxy H]. simpl in *.
    split; auto with ffix.
  Qed.

  Lemma LFixR_trans (x y z : LFix) : LFixR x y -> LFixR y z -> LFixR x z.
  Proof.
    revert y z.
    induction x as [sx Ih].
    intros y z.
    destruct y as [sy]; simpl.
    destruct z as [sz]; simpl.
    intros [Sxy Exy] [Syz Eyz].
    split; [rewrite Sxy; trivial | idtac].
    intros e1 e2 V1.
    destruct (elem_dom_irr Sxy e1) as [e3 V2].
    apply (Ih _ _ _ (Exy _ _ V2)), Eyz.
    rewrite <- V2. trivial.
  Qed.

  #[export] Instance LFix_Eq : equiv LFix :=
    {| eqRel := LFixR;
      e_refl := LFixR_refl;
      e_sym := LFixR_sym;
      e_trans := LFixR_trans;
    |}.

  Lemma l_in_eq  (x y : App F LFix) : x =e y -> LFix_in x =e  LFix_in y.
  Proof. simpl. intros []; auto with ffix. Qed.

  Lemma l_out_eq (x y : LFix) : x =e y -> LFix_out x  =e LFix_out y.
  Proof. destruct x, y. intros []. simpl. auto with ffix. Qed.

  Definition l_in : App F LFix ~> LFix := MkMorph l_in_eq.
  Definition l_out : LFix ~> App F LFix := MkMorph l_out_eq.

  Lemma l_in_out : l_in \o l_out =e id (A:=LFix).
  Proof.
    simpl. intros. split; try reflexivity. intros e1 e2 He.
    rewrite (elem_val_eq He). apply LFixR_refl.
  Qed.

  Lemma l_out_in : l_out \o l_in =e id (A:=App F LFix).
  Proof.
    simpl. intros. split; try reflexivity. intros e1 e2 He.
    rewrite (elem_val_eq He). apply LFixR_refl.
  Qed.

  Definition cata_f `{eA : equiv A} (g : Alg F A) : LFix -> A
    := fix f x := g (fmapA (F:=F) f (LFix_out x)).

  Lemma cata_arr1 `{eA : equiv A} (g : Alg F A)
    : forall x y, x =e y -> cata_f g x =e cata_f g y.
  Proof.
    induction x as [sx Ih]. intros [sy]. simpl in *. intros [Es Ek].
    apply (app_eq g). split; [trivial|intros e1 e2 Hv]. apply Ih. auto.
  Qed.

  Notation cata_ F a
    := (
      {| app := fix f x :=
            a ((fun x => MkCont (F:=F) (shape x)
                           (fun e => f (cont x e))) (LFix_out x));
        app_eq := cata_arr1 a
      |}
    ).

  Lemma cata_arr  `{eA : equiv A}
    : forall f g : Alg F A, f =e g -> cata_ F f =e cata_ F g.
  Proof.
    intros x y E t. induction t as [sx Ih].
    simpl.  rewrite E. apply app_eq. simpl.
    apply cont_ext_eq. intros.
    apply Ih.
  Qed.

  Definition cata `{eA : equiv A} : Alg F A ~> LFix ~> A := MkMorph cata_arr.

  Lemma cata_univ_r `{eA : equiv A} (g : Alg F A) (f : LFix ~> A)
    : f =e g \o fmap f \o l_out -> f =e cata g.
  Proof.
    intros H e. induction e as [e Ih]. simpl in *. rewrite H. apply app_eq.
    split; try auto with ffix. simpl in *. intros e1 e2 Hv. rewrite Ih.
    rewrite (elem_val_eq Hv). reflexivity.
  Qed.

  Lemma cata_univ_l `{eA : equiv A} (g : Alg F A) (f : LFix ~> A)
    : f =e cata g -> f =e g \o fmap f \o l_out.
  Proof.
    intros H [e]. simpl in *. rewrite H. apply app_eq. simpl.
    split; auto with ffix. simpl. intros e1 e2 Hv. rewrite H.
    rewrite (elem_val_eq Hv). reflexivity.
  Qed.

  Lemma cata_univ `{eA : equiv A} (g : Alg F A) (f : LFix ~> A)
    : f =e cata g <-> f =e g \o fmap f \o l_out.
  Proof. split;[apply cata_univ_l|apply cata_univ_r]. Qed.

  Corollary cata_unfold `{eA : equiv A} (g : Alg F A)
    : cata g =e g \o fmap (cata g) \o l_out.
  Proof. rewrite <- cata_univ. reflexivity. Qed.

  Lemma cata_in_id : cata l_in =e id.
  Proof.
    symmetry; apply cata_univ.
    rewrite fmap_id, idKr, l_in_out.
    reflexivity.
  Qed.
End AlgDef.

Arguments l_in & {Sh}%type_scope {Esh} {Po}%type_scope {F}.
Arguments l_out & {Sh}%type_scope {Esh} {Po}%type_scope {F}.
Arguments cata & {Sh}%type_scope {Esh} {Po}%type_scope {F} {A}%type_scope {eA}.
