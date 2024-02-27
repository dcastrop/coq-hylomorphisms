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

  Inductive LFix_ : Type
    := LFix_in { l_shape : Sh; l_cont : Pos l_shape -> LFix_ }.
  Arguments l_cont : clear implicits.

  Fixpoint LFixR_ (x y : LFix_) : Prop :=
    l_shape x =e l_shape y /\
      forall e1 e2, val e1 =e val e2 -> LFixR_ (l_cont x e1) (l_cont y e2).

  Definition lcont_eq (x : LFix_) : Prop :=
    forall e1 e2, e1 =e e2 -> LFixR_ (l_cont x e1) (l_cont x e2).

  Fixpoint Wf (x : LFix_) : Prop := lcont_eq x /\ forall e, Wf (l_cont x e).

  Lemma Wf_cont `(H : Wf x) : forall e, Wf (l_cont x e).
  Proof. destruct x as [sx kx], H; trivial. Qed.
  Lemma Wf_eq `(H : Wf x) : lcont_eq x.
  Proof. destruct x as [sx kx], H; trivial. Qed.

  Record LFix := WfLFix { lfix :> LFix_; WF_lfix : Wf lfix }.
  Definition LFixR (x y : LFix) := LFixR_ (lfix x) (lfix y).

  Lemma LFixR_refl (x : LFix) : LFixR x x.
  Proof.
    destruct x as [[sx kx] WFx]; unfold LFixR.
    split; try reflexivity. intros e1 e2 Heq. apply Wf_eq; trivial.
  Qed.

  Lemma LFixR_sym (x y : LFix) : LFixR x y -> LFixR y x.
  Proof.
    destruct x as [x WFx], y as [y WFy]; revert WFx y WFy. unfold LFixR.
    simpl. induction x as [sx kx IH]. destruct y as [sy ky]. simpl.
    unfold lcont_eq; simpl. intros [Keq WFy] [Sxy H].
    split; auto with ffix. intros e1 e2 Hv. apply IH; auto with ffix.
    apply WFx.
  Qed.

  Lemma LFixR_trans (x y z : LFix) : LFixR x y -> LFixR y z -> LFixR x z.
  Proof.
    destruct x as [x WFx], y as [y WFy], z as [z WFz].
    revert WFx y WFy z WFz. unfold LFixR; simpl in *.
    induction x as [sx kx IH].
    intros [Kx WFx] [sy ky] [_ WFy] [sz kz] [_ WFz].
    unfold lcont_eq in *; simpl in *. intros [Sxy Exy] [Syz Eyz].
    split; [rewrite Sxy; trivial | idtac].
    intros e1 e2 V1. destruct (elem_valid_irr Sxy e1) as [e3 V2].
    apply (IH e1 (WFx _) _ (WFy _) _ (WFz _) (Exy _ _ V2)), Eyz.
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

  Definition cata_f `{eA : equiv A} (g : Alg F A) : LFix -> A
    := fix f (x : LFix) :=
      match x with
      | LFix_in ax =>
          let (sx, kx) := ax in
          g (MkCont sx (fun e => f (kx e)))
      end.

  Lemma cata_arr1 `{eA : equiv A} (g : Alg F A)
    : forall x y, x =e y -> cata_f g x =e cata_f g y.
  Proof.
    induction x as [sx Ih]. intros [sy]. simpl in *. intros [Es Ek].
    destruct sx as [sx kx]. destruct sy as [sy ky]. simpl in *.
    apply (app_eq g). split; [trivial|intros e1 e2 Hv]. apply Ih. auto.
  Qed.

  Definition cata_ `{equiv A} (a : Alg F A) :=
      {| app :=
          fix f (x : LFix) :=
            match x with
            | LFix_in ax =>
                let (sx, kx) := ax in
                a (MkCont sx (fun e => f (kx e)))
            end;
        app_eq := cata_arr1 a
      |}.

  Lemma cata_arr  `{eA : equiv A}
    : forall f g : Alg F A, f =e g -> cata_ f =e cata_ g.
  Proof.
    intros x y E t. induction t as [sx Ih]. unfold cata_.
    destruct sx as [sx kx].  simpl in *.
    rewrite E. apply app_eq. simpl.
    apply cont_ext_eq. intros.
    apply Ih.
  Qed.

  Definition cata `{eA : equiv A} : Alg F A ~> LFix ~> A :=
    Eval unfold cata_ in MkMorph cata_arr.

  Lemma cata_univ_r `{eA : equiv A} (g : Alg F A) (f : LFix ~> A)
    : f =e g \o fmap f \o l_out -> f =e cata g.
  Proof.
    intros H e. induction e as [e Ih]. destruct e as [se ke].
    simpl in *. rewrite H. apply app_eq.
    split; try auto with ffix. simpl in *. intros e1 e2 Hv. rewrite Ih.
    rewrite (elem_val_eq Hv). reflexivity.
  Qed.

  Lemma cata_univ_l `{eA : equiv A} (g : Alg F A) (f : LFix ~> A)
    : f =e cata g -> f =e g \o fmap f \o l_out.
  Proof.
    intros H [e]. simpl in *. rewrite H. destruct e as [se ke].
    apply app_eq. simpl.
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
