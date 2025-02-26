Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import HYLO.Equivalence.
Require Import HYLO.Morphism.
Require Import HYLO.Container.

Notation Alg F A := (App F A ~> A).

Section AlgDef.
  Context `(F : Cont Sh Po).

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
    destruct (elem_valid_irr Sxy e1) as [e3 V2].
    apply (Ih _ _ _ (Exy _ _ V2)), Eyz.
    rewrite <- V2. trivial.
  Qed.

  #[export] Instance LFix_Eq : setoid LFix :=
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

  Definition cata_f `{eA : setoid A} (g : Alg F A) : LFix -> A
    := fix f (x : LFix) :=
      match x with
      | LFix_in ax =>
          let (sx, kx) := ax in
          g (MkCont sx (fun e => f (kx e)))
      end.

  Lemma cata_arr1 `{eA : setoid A} (g : Alg F A)
    : forall x y, x =e y -> cata_f g x =e cata_f g y.
  Proof.
    induction x as [sx Ih]. intros [sy]. simpl in *. intros [Es Ek].
    destruct sx as [sx kx]. destruct sy as [sy ky]. simpl in *.
    apply (app_eq g). split; [trivial|intros e1 e2 Hv]. apply Ih. auto.
  Qed.

  Definition cata_ `{setoid A} (a : Alg F A) :=
      {| app :=
          fix f (x : LFix) :=
            match x with
            | LFix_in ax =>
                let (sx, kx) := ax in
                a (MkCont sx (fun e => f (kx e)))
            end;
        app_eq := cata_arr1 a
      |}.

  Lemma cata_arr  `{eA : setoid A}
    : forall f g : Alg F A, f =e g -> cata_ f =e cata_ g.
  Proof.
    intros x y E t. induction t as [sx Ih]. unfold cata_.
    destruct sx as [sx kx].  simpl in *.
    rewrite E. apply app_eq. simpl.
    apply cont_ext_eq. intros.
    apply Ih.
  Qed.

  Definition cata `{eA : setoid A} : Alg F A ~> LFix ~> A :=
    Eval unfold cata_ in MkMorph cata_arr.

  Lemma cata_univ_r `{eA : setoid A} (g : Alg F A) (f : LFix ~> A)
    : f =e g \o fmap f \o l_out -> f =e cata g.
  Proof.
    intros H e. induction e as [e Ih]. destruct e as [se ke].
    simpl in *. rewrite H. apply app_eq.
    split; try auto with ffix. simpl in *. intros e1 e2 Hv. rewrite Ih.
    rewrite (elem_val_eq Hv). reflexivity.
  Qed.

  Lemma cata_univ_l `{eA : setoid A} (g : Alg F A) (f : LFix ~> A)
    : f =e cata g -> f =e g \o fmap f \o l_out.
  Proof.
    intros H [e]. simpl in *. rewrite H. destruct e as [se ke].
    apply app_eq. simpl.
    split; auto with ffix. simpl. intros e1 e2 Hv. rewrite H.
    rewrite (elem_val_eq Hv). reflexivity.
  Qed.

  Lemma cata_univ `{eA : setoid A} (g : Alg F A) (f : LFix ~> A)
    : f =e cata g <-> f =e g \o fmap f \o l_out.
  Proof. split;[apply cata_univ_l|apply cata_univ_r]. Qed.

  Corollary cata_unfold `{eA : setoid A} (g : Alg F A)
    : cata g =e g \o fmap (cata g) \o l_out.
  Proof. rewrite <- cata_univ. reflexivity. Qed.

  Lemma cata_in_id : cata l_in =e id.
  Proof.
    symmetry; apply cata_univ.
    rewrite fmap_id, idKr, l_in_out.
    reflexivity.
  Qed.
End AlgDef.

Arguments l_in & {Sh}%_type_scope {Esh} {Po}%_type_scope {F}.
Arguments l_out & {Sh}%_type_scope {Esh} {Po}%_type_scope {F}.
Arguments cata & {Sh}%_type_scope {Esh} {Po}%_type_scope {F} {A}%_type_scope {eA}.
