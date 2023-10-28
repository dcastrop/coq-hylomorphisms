Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import HYLO.Equivalence.
Require Import HYLO.Morphism.
Require Import HYLO.Container.

Definition Alg `{F : Container Sh P} A {eA : equiv A} := App F A ~> A.
Arguments Alg {Sh}%type_scope {Esh} {P}%type_scope F A {eA}.
Definition CoAlg `{F : Container Sh P} A {eA : equiv A} := A ~> App F A.
Arguments CoAlg {Sh}%type_scope {Esh} {P}%type_scope F A {eA}.

Unset Elimination Schemes.
#[universes(template)]
  Inductive LFix `(F : Container Sh P) : Type :=
  LFix_in { LFix_out : App F (LFix F) }.
Set Elimination Schemes.
Arguments LFix {Sh}%type_scope {Esh} {P}%type_scope F.

Lemma LFix_rect [Sh : Type] [Esh : equiv Sh] [Po : Type]
  [F : Container Sh Po] [P : LFix F -> Type]
  : (forall x : App F (LFix F),
        (forall e : Pos (shape x), P (cont x e)) ->
        P (LFix_in x))
    -> forall l : LFix F, P l.
Proof.
  intros H. fix Ih 1. intros []. apply H. intros e. apply Ih. Guarded.
Defined.

Lemma LFix_rec [Sh : Type] [Esh : equiv Sh] [Po : Type]
  [F : Container Sh Po] [P : LFix F -> Set]
  : (forall x : App F (LFix F),
        (forall e : Pos (shape x), P (cont x e)) ->
        P (LFix_in x))
    -> forall l : LFix F, P l.
Proof.
  intros H. apply LFix_rect, H.
Defined.

Lemma LFix_ind [Sh : Type] [Esh : equiv Sh] [Po : Type]
  [F : Container Sh Po] [P : LFix F -> Prop]
  : (forall x : App F (LFix F),
        (forall e : Pos (shape x), P (cont x e)) ->
        P (LFix_in x))
    -> forall l : LFix F, P l.
Proof.
  intros H. apply LFix_rect, H.
Qed.

Fixpoint LFixR `(F : Container Sh P) (x y : LFix F) : Prop :=
  let f_x := LFix_out x in
  let f_y := LFix_out y in
  shape f_x =e shape f_y /\
  (forall e1 e2, val e1 = val e2 -> LFixR (cont f_x e1) (cont f_y e2)).

Lemma LFixR_refl `{F : Container Sh P} (x : LFix F) : LFixR x x.
Proof.
  induction x as [x Ih]. simpl. split; try reflexivity.
  intros e1 e2 Heq. rewrite (elem_val_eq Heq). apply Ih.
Qed.

Lemma LFixR_sym `{F : Container Sh P} (x y : LFix F) : LFixR x y -> LFixR y x.
Proof.
  revert y. induction x as [x Ih].
  intros [y] [Sxy H]. simpl in *.
  split; auto with ffix.
Qed.

Lemma LFixR_trans `{F : Container Sh P} (x y z : LFix F)
  : LFixR x y -> LFixR y z -> LFixR x z.
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

#[export] Instance LFix_Eq `{F : Container Sh P} : equiv (LFix F) :=
  {| eqRel := LFixR (F:=F);
     e_refl := LFixR_refl (F:=F);
     e_sym := LFixR_sym (F:=F);
     e_trans := LFixR_trans (F:=F);
  |}.

Lemma l_in_eq `{F : Container Sh P} (x y : App F (LFix F))
  : x =e y -> LFix_in x =e  LFix_in y.
Proof. simpl. intros []; auto with ffix. Qed.

Lemma l_out_eq `(F : Container Sh P) (x y : LFix F)
  : x =e y -> LFix_out x  =e LFix_out y.
Proof. destruct x, y. intros []. simpl. auto with ffix. Qed.

Definition l_in `{F : Container Sh P} : Alg F (LFix F) :=
  {| app := _; app_eq := l_in_eq (F:=F) |}.
Definition l_out `{F : Container Sh P} : CoAlg F (LFix F) :=
  {| app := _; app_eq := l_out_eq (F:=F) |}.

Lemma l_in_out `(F : Container Sh P) : l_in \o l_out =e id (A:=LFix F).
Proof.
  simpl. intros. split; try reflexivity. intros e1 e2 He.
  rewrite (elem_val_eq He). apply LFixR_refl.
Qed.

Lemma l_out_in `(F : Container Sh P) : l_out \o l_in =e id (A:=App F (LFix F)).
Proof.
  simpl. intros. split; try reflexivity. intros e1 e2 He.
  rewrite (elem_val_eq He). apply LFixR_refl.
Qed.

Definition cata_f `{F : Container Sh P} A {eA : equiv A} (g : Alg F A)
  : LFix F -> A
  := fix f x := g (fmapA (F:=F) f (LFix_out (F:=F) x)).
Arguments cata_f {Sh Esh P F A eA} g.

Lemma cata_arr `{F : Container Sh P} A {eA : equiv A} (g : Alg F A)
  : forall x y, x =e y -> cata_f g x =e cata_f g y.
Proof.
  induction x as [sx Ih]. intros [sy]. simpl in *. intros [Es Ek].
  apply (app_eq g). split; [trivial|intros e1 e2 Hv]. apply Ih. auto.
Qed.

Definition cata `{F : Container Sh P} A {eA : equiv A} (g : Alg F A)
  : LFix F ~> A
  := {| app := fix f x :=
           g ((fun x => MkCont (F:=F) (shape x)
                          (fun e => f (cont x e))) (LFix_out (F:=F) x));
       app_eq := cata_arr g |}.
Arguments cata {Sh}%type_scope {Esh} {P}%type_scope {F} [A]%type_scope {eA} g.

Lemma cata_univ_r `{F : Container Sh P} `{eA : equiv A} (g : Alg F A)
      (f : LFix F ~> A)
  : f =e g \o fmap f \o l_out -> f =e cata g.
Proof.
  intros H e. induction e as [e Ih]. simpl in *. rewrite H. apply app_eq.
  split; try auto with ffix. simpl in *. intros e1 e2 Hv. rewrite Ih.
  rewrite (elem_val_eq Hv). reflexivity.
Qed.

Lemma cata_univ_l `{F : Container Sh P} `{eA : equiv A} (g : Alg F A)
      (f : LFix F ~> A)
  : f =e cata g -> f =e g \o fmap f \o l_out.
Proof.
  intros H [e]. simpl in *. rewrite H. apply app_eq. simpl.
  split; auto with ffix. simpl. intros e1 e2 Hv. rewrite H.
  rewrite (elem_val_eq Hv). reflexivity.
Qed.

Lemma cata_univ `{F : Container Sh P} `{eA : equiv A} (g : Alg F A)
      (f : LFix F ~> A)
  : f =e cata g <-> f =e g \o fmap f \o l_out.
Proof. split;[apply cata_univ_l|apply cata_univ_r]. Qed.

(* Terminating anamorphisms *)
Inductive FinF `{F : Container Sh P} `{equiv A}
          (h : CoAlg F A) : A -> Prop :=
| FinF_fold x : (forall e, FinF h (cont (h x) e)) -> FinF h x.
#[export] Hint Constructors FinF : ffix.

Lemma FinF_inv `{F : Container Sh P} `{eA : equiv A} (h : CoAlg F A) x
  : FinF h x -> forall e, FinF h (cont (h x) e).
Proof. intros []. auto. Defined.

(* Finite coalgebras *)
Definition FCoAlg `{F : Container Sh P} `{equiv A} :=
  sig (fun f => forall x, FinF (F:=F) f x).
Arguments FCoAlg {Sh Esh P} F A {eA} : rename.

Coercion coalg `{F : Container Sh P} `{equiv A}
  : FCoAlg F A -> A ~> App F A := @proj1_sig _ _.

Definition finite `{F : Container Sh P} `{equiv A}
  : forall (h : FCoAlg F A) x, FinF h x := @proj2_sig _ _.

Definition ana_f_ `{F : Container Sh P} `{eA : equiv A} (h : CoAlg F A)
  : forall (x : A), FinF h x -> LFix F
  := fix f x H :=
       let hx := h x in
       LFix_in (MkCont (shape hx) (fun e => f (cont hx e) (FinF_inv H e))).

Lemma ana_f_irr `{F : Container Sh P} `{eA : equiv A} (h : CoAlg F A)
  : forall (x : A) (F1 F2 : FinF h x), ana_f_ F1 =e ana_f_ F2.
Proof.
  simpl. fix Ih 2. intros x0 [x Fx] F2. clear x0. destruct F2 as [x Fy].
  simpl. split; [reflexivity| intros e1 e2 d]. rewrite (elem_val_eq d).
  apply Ih. Guarded.
Qed.

Definition ana_f `{F : Container Sh P} `{eA : equiv A} (h : FCoAlg F A)
  : A -> LFix F
  := fun x => ana_f_ (finite h x).

Lemma ana_arr `{F : Container Sh P} `{eA : equiv A} (h : FCoAlg F A)
  : forall x y, x =e y -> ana_f h x =e ana_f h y.
Proof.
  unfold ana_f. intros x y. generalize (finite h x) (finite h y). revert x y.
  fix Ih 3. intros x y [x' Fx] [y' Fy] Hxy. simpl. split.
  - destruct (app_eq h Hxy). auto.
  - intros e d1 d2. simpl. apply Ih. Guarded.
    destruct (app_eq h Hxy). auto.
Qed.

Lemma LFixR_fold `{F : Container Sh P} (x y : LFix F) : LFixR x y = (x =e y).
Proof. auto. Qed.

Definition ana `(F : Container Sh P) A (eA : equiv A)
           (h : FCoAlg F A) : A ~> LFix F
  := {| app := fun x =>
                 (fix f x H :=
                    let hx := h x in
                    LFix_in (MkCont (shape hx)
                               (fun e => f (cont hx e) (FinF_inv H e)))
                 ) x (finite h x);
       app_eq := ana_arr h
     |}.

Lemma ana_univ_r `(F : Container Sh P) A (eA : equiv A)
      (h : FCoAlg F A) (f : A ~> LFix F)
  : f =e l_in \o fmap f \o h -> f =e ana h.
Proof.
  intros H. unfold ana, ana_f. simpl. intros x. generalize (finite h x).
  revert x.  fix Ih 2. intros x0 [x Fx]. clear x0.
  rewrite LFixR_fold, (H _). simpl.
  split; [reflexivity| intros d1 d2 e]. rewrite (elem_val_eq e). apply Ih.
Qed.

Lemma ana_univ_l `{F : Container Sh P} A {eA : equiv A}
      (h : FCoAlg F A) (f : A ~> LFix F)
  : f =e ana h -> f =e l_in \o fmap f \o h.
Proof.
  intros H x0. rewrite (H _). simpl. unfold ana_f.
  generalize (finite h x0) as Fx. intros [x Fx]. clear x0. simpl.
  split; [reflexivity| intros d1 d2 e]. rewrite (elem_val_eq e).
  generalize (H (cont (coalg h x) d2)). simpl. rewrite !LFixR_fold.
  intros Hrw. rewrite Hrw. apply ana_f_irr.
Qed.

Lemma ana_univ `{F : Container Sh P} A {eA : equiv A}
      (h : FCoAlg F A) (f : A ~> LFix F)
  : f =e ana h <-> f =e l_in \o fmap f \o h.
Proof. split;[apply ana_univ_l|apply ana_univ_r]. Qed.
