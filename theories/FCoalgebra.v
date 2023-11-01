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

  Definition RecP `{eA : equiv A} (c : Coalg F A) := forall x, RecF c x.

  Add Parametric Morphism `{eA : equiv A} : (@RecP A eA)
    with signature
    (eqRel (A := Coalg F A))
      ==> (eqRel (A:=Prop))
      as RecPMorphism.
  Proof.
    intros f g H. simpl; split.
    - intros Pf x. rewrite <- H. trivial.
    - intros Pf x. rewrite    H. trivial.
  Qed.

  Record RCoalg `{eA : equiv A} :=
    Rec {
        coalg :> Coalg F A;
        recP : RecP coalg
      }.
  Arguments RCoalg A {eA}.
  Arguments Rec {A eA} coalg recP.

  #[export] Instance equiv_rcoalg `{equiv A} : equiv (RCoalg A).
  Proof with auto with ffix.
    refine {|
        eqRel := fun x y => coalg x =e coalg y
      |}...
    intros x y z H1 H2. transitivity y...
  Defined.

  Lemma terminating `{equiv A} : forall (h : RCoalg A) x, RecF h x.
  Proof. destruct h. trivial. Qed.


  (* Finite Trees *)
  Inductive FinF : GFix F -> Prop :=
  | FinF_fold (x : GFix F) : (forall e, FinF (cont (g_out x) e)) -> FinF x.

  Lemma FinF_inv (x : GFix F) : FinF x -> forall e, FinF (cont (g_out x) e).
  Proof. intros []. auto. Defined.

  Lemma ana_rcoalg_fin `{equiv A} (c : Coalg F A) (Rc : RecP c)
    : forall x, FinF (ana c x).
  Proof.
    simpl. intros x. generalize (Rc x).
    intros Rcx. induction Rcx as [x _ Ih]. constructor. simpl in *.
    rewrite unfold_ana_f. simpl. exact Ih.
  Qed.

  Lemma fin_ana_rcoalg `{equiv A}
    (h : Coalg F A) (FT : forall x, FinF (ana h x)) : RecP h.
  Proof.
    intros x. specialize (FT x). revert FT.
    generalize (eq_refl (ana h x)). generalize (ana h x) at -1. intros g Eg HF.
    revert x Eg. induction HF as [g _ Ih]. intros x Eg. subst. simpl in *.
    rewrite unfold_ana_f in *. simpl in *. constructor. intros e.
    specialize (Ih e _ eq_refl). trivial.
  Qed.

  Corollary ana_rec_term `{equiv A} (h : Coalg F A)
    : (forall x, FinF (ana h x)) <-> RecP h.
  Proof. split; try apply ana_rcoalg_fin; apply fin_ana_rcoalg. Qed.

  Corollary rcoalg_fin `{equiv A} (h : RCoalg A) : forall x, FinF (ana h x).
  Proof. apply ana_rcoalg_fin. destruct h; trivial. Qed.

  Lemma fin_out : forall x, RecF l_out x.
  Proof. induction x as [s Ih]. constructor. apply Ih. Qed.

  Definition f_out : RCoalg (LFix F) := Rec _ fin_out.

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

  Corollary rana_unfold A {eA : equiv A} (h : RCoalg A)
    : rana h =e l_in \o fmap (rana h) \o h.
  Proof. rewrite <- rana_univ. reflexivity. Qed.
End FCoalgDef.
Arguments RCoalg {Sh Esh P} F A {eA}.

Arguments rana & {Sh}%type_scope {Esh} {P}%type_scope {F} {A}%type_scope {eA}.

Arguments f_out & {Sh}%type_scope {Esh} {P}%type_scope {F}.

Section CAlgDef.
  Context `{F : Container Sh Po}.

  Definition ccata_f_ `{eA : equiv A} (g : Alg F A)
    : forall x : GFix F, FinF x -> A
    := fix f x H :=
      let hx := g_out x in
      g (MkCont (shape hx) (fun e => f (cont hx e) (FinF_inv H e))).

  Lemma ccata_f_irr `{eA : equiv A} (h : Alg F A)
    : forall x (F1 F2 : FinF x), ccata_f_ h F1 =e ccata_f_ h F2.
  Proof.
    fix Ih 2. intros x F1 F2. destruct F1 as [x F1]. destruct F2 as [x F2].
    apply app_eq. simpl. constructor; simpl; try reflexivity.
    intros e1 e2 Hv. rewrite (elem_val_eq Hv). apply Ih. Guarded.
  Qed.

  Definition ccata_f `{eA : equiv A} (g : Alg F A) : {x : GFix F | FinF x} -> A
    := fun x => ccata_f_ g (proj2_sig x).

  Lemma ccata_arr1 `{eA : equiv A} (g : Alg F A)
    : forall x y, x =e y -> ccata_f g x =e ccata_f g y.
  Proof.
    intros [x Fx] [y Fy] Rxy. simpl in *.
    unfold ccata_f. simpl. revert x y Fx Fy Rxy. fix Ih 3. intros x y Fx Fy.
    destruct Fx as [x Fx]. destruct Fy as [y Fy]. simpl in *.
    intros Rxy. apply GFixR_unfold in Rxy. destruct Rxy as [ES EK].
    apply app_eq. simpl. constructor; simpl; trivial. intros e1 e2 Hv.
    apply Ih. Guarded.
    apply EK. trivial.
  Qed.

  Definition ccata_ `{eA : equiv A} g : {x : GFix F | FinF x} ~> A
    := MkMorph (ccata_arr1 g).

  Lemma ccata_arr `{eA : equiv A}
    : forall x y : Alg F A, x =e y -> ccata_ x =e ccata_ y.
  Proof.
    intros x y Hxy [g Fg]. unfold ccata_, ccata_f. simpl.
    revert g Fg. fix Ih 2. intros g Fg. destruct Fg as [ES EK]. simpl.
    rewrite Hxy. apply app_eq. constructor; simpl; auto with ffix.
    intros e1 e2 Hv. rewrite (elem_val_eq Hv). apply Ih.
  Qed.

  Definition ccata `{eA : equiv A} : Alg F A ~> {x : GFix F | FinF x} ~> A
    := MkMorph ccata_arr.

  Definition lg_out_ (x : GFix F | FinF x) : App F {x : GFix F | FinF x}
    := let hx := g_out (proj1_sig x) in
       MkCont (shape hx)
         (fun e => exist (fun ex => _) (cont hx e) (FinF_inv (proj2_sig x) e)).

  Lemma lg_out_arr : forall x y, x =e y -> lg_out_ x =e lg_out_ y.
  Proof.
    intros [x Fx] [y Fy] Rxy. simpl in *.
    destruct (GFixR_unfold Rxy) as [Sxy Kxy].
    constructor; trivial.
  Qed.

  Definition lg_out : {x : GFix F | FinF x} ~> App F {x : GFix F | FinF x}
    := MkMorph lg_out_arr.

  Definition lg_in_ (x : App F {g : GFix F | FinF g}) : {x : GFix F | FinF x}
    := let gx := g_in (MkCont (shape x) (fun e => proj1_sig (cont x e))) in
       exist (fun g => _) gx
         (FinF_fold (fun e : Pos (shape (g_out gx)) => proj2_sig (cont x e))).

  Lemma lg_in_arr : forall x y, x =e y -> lg_in_ x =e lg_in_ y.
  Proof.
    intros [Sx Kx] [Sy Ky] [Sxy Kxy]. simpl in *.
    apply GFixR_in; simpl; trivial.
  Qed.

  Definition lg_in : App F {g : GFix F | FinF g} ~> {x : GFix F | FinF x}
    := MkMorph lg_in_arr.

  Lemma lg_in_out : lg_in \o lg_out =e id.
  Proof.
    intros [g Pg]. simpl. apply GFixR_in; simpl; try reflexivity.
    intros e1 e2 Hv. rewrite (elem_val_eq Hv). apply GFixR_refl.
  Qed.

  Lemma lg_out_in : lg_out \o lg_in =e id.
  Proof.
    intros [Sx Kx]. simpl. constructor; simpl; try reflexivity.
    intros e1 e2 Hv. rewrite (elem_val_eq Hv). apply GFixR_refl.
  Qed.

  Lemma ccata_univ_r `{eA : equiv A} (g : Alg F A)
    (f : {x : GFix F | FinF x} ~> A)
    : f =e g \o fmap f \o lg_out -> f =e ccata g.
  Proof.
    intros H [e Fe]. simpl. unfold ccata_f. simpl.
    revert e Fe. fix Ih 2. intros e Fe. destruct Fe as [e Fe].
    rewrite H. simpl. apply app_eq. constructor; simpl; try reflexivity.
    intros e1 e2 Hv. rewrite (elem_val_eq Hv). apply Ih.
  Qed.

  Lemma ccata_univ_l `{eA : equiv A} (g : Alg F A)
    (f : {x : GFix F | FinF x} ~> A)
    : f =e ccata g -> f =e g \o fmap f \o lg_out.
  Proof.
    intros ->. clear f. intros [x Fx]. simpl. unfold ccata_f. simpl.
    destruct Fx as [x Fx]. simpl. reflexivity.
  Qed.

  Lemma ccata_univ `{eA : equiv A} (g : Alg F A)
    (f : {x : GFix F | FinF x} ~> A)
    : f =e ccata g <-> f =e g \o fmap f \o lg_out.
  Proof. split;[apply ccata_univ_l|apply ccata_univ_r]. Qed.

  Corollary ccata_unfold `{eA : equiv A} (g : Alg F A)
    : ccata g =e g \o fmap (ccata g) \o lg_out.
  Proof. rewrite <- ccata_univ. reflexivity. Qed.

  Lemma ccata_in_id : ccata lg_in =e id.
  Proof.
    symmetry; apply ccata_univ.
    rewrite fmap_id, idKr, lg_in_out.
    reflexivity.
  Qed.
End CAlgDef.

Section FinRec.
  Context `{F : Container Sh Po}.

  Lemma cata_ccata `{equiv A} (f : Alg F A) : cata f \o ccata l_in =e ccata f.
  Proof.
    apply ccata_univ.
    rewrite fmap_comp, <- (idKl (fmap (ccata _))), <- l_out_in.
    rewrite compA, compA, compA.
    rewrite <- cata_unfold.
    rewrite <- compA, <- compA, (compA l_in).
    rewrite <- ccata_unfold.
    reflexivity.
  Qed.

  Lemma ccata_cata `{equiv A} (f : Alg F A) : ccata f \o cata lg_in =e cata f.
  Proof.
    apply cata_univ.
    rewrite fmap_comp, <- (idKl (fmap (cata _))), <- lg_out_in.
    rewrite compA, compA, compA.
    rewrite <- ccata_unfold.
    rewrite <- compA, <- compA, (compA lg_in).
    rewrite <- cata_unfold.
    reflexivity.
  Qed.

  Definition f_to_fg : LFix F ~> {x : GFix F | FinF x} := cata lg_in.
  Definition fg_to_f : {x : GFix F | FinF x} ~> LFix F := ccata l_in.

  Corollary fg_to_fI : fg_to_f \o f_to_fg =e id.
  Proof.
    unfold fg_to_f, f_to_fg.
    rewrite <- cata_in_id. apply ccata_cata.
  Qed.

  Corollary f_to_fgI : f_to_fg \o fg_to_f =e id.
  Proof.
    unfold fg_to_f, f_to_fg.
    rewrite <- ccata_in_id. apply cata_ccata.
  Qed.


  Lemma ccata_ana_r `{equiv A}
    (f : A ~> GFix F) (Ff : forall x, FinF (f x)) (g : A ~> LFix F)
    : ccata l_in \o liftP f Ff =e g -> f =e ana f_out \o g.
  Proof.
    unfold liftP,liftP_f_. simpl. unfold ccata_f.  simpl. intros Hx x.
    specialize (Hx x). generalize dependent (Ff x). generalize (g x) (f x).
    clear Ff f g x.
    intros l. induction l as [l Ih]. intros y Fy. destruct Fy as [y Fy].
    simpl in *. intros [Sfg Rk].
    apply GFixR_in; trivial. rewrite unfold_ana_f. simpl. intros e1 e2 Hv.
    apply Ih with (f:=Fy e1), Rk, Hv.
  Qed.

  Lemma ccata_ana_l `{equiv A}
    (f : A ~> GFix F) (Ff : forall x, FinF (f x)) (g : A ~> LFix F)
    : f =e ana f_out \o g -> ccata l_in \o liftP f Ff =e g.
  Proof.
    unfold liftP,liftP_f_. simpl. unfold ccata_f.  simpl. intros Hx x.
    specialize (Hx x). revert Hx. generalize (g x) (f x) (Ff x).
    clear f Ff g x. induction l as [l Ih]. intros g Ff.
    destruct Ff as [g Fg]. intros Hg. simpl in *.
    apply GFixR_unfold in Hg. rewrite unfold_ana_f in *. simpl in *.
    destruct Hg as [Sg Kg]. split; trivial. intros e1 e2 Hv.
    apply Ih, Kg, Hv.
  Qed.

  Lemma ccata_ana `{equiv A}
    (f : A ~> GFix F) (Ff : forall x, FinF (f x)) (g : A ~> LFix F)
    : f =e ana f_out \o g <-> ccata l_in \o liftP f Ff =e g.
  Proof. split; [apply ccata_ana_l| apply ccata_ana_r]. Qed.

  Lemma rana_ana `{equiv A} (f : RCoalg F A) : ana f =e ana f_out \o rana f.
  Proof.
    symmetry. apply ana_univ.
    rewrite fmap_comp, <- (idKl (fmap (rana _))), <- l_out_in.
    rewrite compA, compA, compA.
    rewrite <- ana_unfold.
    rewrite <- compA, <- compA, (compA l_in).
    rewrite <- rana_unfold.
    reflexivity.
  Qed.

  Corollary ana_rana `{equiv A} (f : RCoalg F A)
    : ccata l_in \o liftP (ana f) (rcoalg_fin f) =e rana f.
  Proof. rewrite <- ccata_ana. apply rana_ana. Qed.
End FinRec.
