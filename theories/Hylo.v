Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import HYLO.Equivalence.
Require Import HYLO.Morphism.
Require Import HYLO.Container.
Require Import HYLO.Algebra.
Require Import HYLO.Coalgebra.
Require Import HYLO.FCoalgebra.

Definition hylo_f_ `{F : Container Sh P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg F B) (h : Coalg F A)
  : forall (x : A), RecF h x -> B
  := fix f x H :=
       match h x as h0
             return
             (forall e : Pos (shape h0), RecF h (cont h0 e)) ->
             B
       with
       | MkCont s_x c_x => fun H => g (MkCont s_x (fun e => f (c_x e) (H e)))
       end (RecF_inv H).

Lemma hylo_f_irr `{F : Container Sh P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg F B) (h : Coalg F A)
  : forall (x : A) (F1 F2 : RecF h x), hylo_f_ g F1 =e hylo_f_ g F2.
Proof.
  fix Ih 2. intros x0 [x Fx] F2. clear x0. destruct F2 as [x Fy]. simpl.
  generalize dependent (h x).  clear x. intros [s_x c_x] Fx Fy. simpl in *.
  apply app_eq. split; [reflexivity|intros d1 d2 e].
  rewrite (elem_val_eq e). simpl in *. apply Ih. Guarded.
Qed.

Definition hylo_f `{F : Container Sh P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg F B) (h : RCoalg F A)
  := fun x => hylo_f_ g (terminating h x).

Lemma hylo_arr `{F : Container Sh P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg F B) (h : RCoalg F A)
  : forall x y, x =e y -> hylo_f g h x =e hylo_f g h y.
Proof.
  unfold hylo_f.
  intros x y. generalize x,y,(terminating h x),(terminating h y). clear x y.
  fix Ih 3. intros x y [x' Fx] [y' Fy] H. simpl.
  generalize (@app_eq _ _ _ _ h _ _ H). revert Fx Fy.
  generalize (h x') (h y'). intros [s_x c_x] [s_y c_y]. simpl.
  intros Fx Fy [Exy Ec]. simpl in *.
  apply app_eq. split; [trivial|simpl; intros d1 d2 e].
  apply Ih. Guarded. apply Ec, e.
Qed.

Definition hylo `{F : Container Sh P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg F B) (h : RCoalg F A)
  : A ~> B
  := {| app :=
         fun x =>
           (fix f x H :=
              match h x as h0
                    return
                    (forall e : Pos (shape h0), RecF h (cont h0 e)) ->
                    B
              with
              | MkCont s_x c_x =>
                  fun H => g (MkCont s_x (fun e => f (c_x e) (H e)))
              end (RecF_inv H)) x (terminating h x);
       app_eq := hylo_arr g h |}.

(* "universal" (quotes) because these are *terminating* hylos, otherwise this
   direction would not work
 *)
Lemma hylo_univ_r `{F : Container Sh P}
      A B {eA : equiv A} {eB : equiv B}
      (g : Alg F B) (h : RCoalg F A) (f : A ~> B)
  : f =e g \o fmap f \o h -> f =e hylo g h.
Proof.
  intros H. unfold hylo, hylo_f. simpl.
  intros x. generalize x, (terminating h x). clear x.
  fix Ih 2. intros x Fx. rewrite (H _). simpl. unfold comp. unfold fmap.
  destruct Fx as [x Fx]. simpl. destruct (h x) as [s_x c_x]. simpl in *.
  apply app_eq. simpl. split; [reflexivity|simpl; intros d1 d2 e].
  rewrite (elem_val_eq e). apply Ih. Guarded.
Qed.

Lemma hylo_univ_l `{F : Container Sh P}
      A B {eA : equiv A} {eB : equiv B}
      (g : Alg F B) (h : RCoalg F A) (f : A ~> B)
  : f =e hylo g h -> f =e g \o fmap f \o h.
Proof.
  intros H. rewrite H. clear H f. simpl. intros x.
  destruct (terminating h x) as [x Fx]. simpl.
  destruct (h x) as [s_x c_x]. simpl in *.
  apply app_eq. split; [reflexivity|simpl; intros d1 d2 e].
  rewrite (elem_val_eq e). apply hylo_f_irr.
Qed.

Lemma hylo_univ `{F : Container Sh P}
      A B {eA : equiv A} {eB : equiv B}
      (g : Alg F B) (h : RCoalg F A) (f : A ~> B)
  : f =e hylo g h <-> f =e g \o fmap f \o h.
Proof. split;[apply hylo_univ_l|apply hylo_univ_r]. Qed.

Corollary hylo_unr `{F : Container Sh P}
      A B {eA : equiv A} {eB : equiv B}
      (g : Alg F B) (h : RCoalg F A)
  : hylo g h =e g \o fmap (hylo g h) \o h.
Proof. rewrite <-hylo_univ. reflexivity. Qed.

Lemma fin_out `(F : Container Sh P) : forall x, RecF (F:=F) l_out x.
Proof. induction x as [s Ih]. constructor. apply Ih. Qed.

Definition f_out `(F : Container Sh P) : RCoalg F (LFix F) :=
  exist _ _ (fin_out (F:=F)).
Arguments f_out & {Sh}%type_scope {Esh} {P}%type_scope {F}.

Lemma hylo_cata `{F : Container Sh P} B {eB : equiv B} (g : Alg F B)
  : cata g =e hylo g f_out.
Proof. rewrite hylo_univ. apply cata_univ. reflexivity. Qed.

Lemma hylo_ana `{F : Container Sh P} A {eA : equiv A} (h : RCoalg F A)
  : rana h =e hylo l_in h.
Proof. rewrite hylo_univ. apply rana_univ. reflexivity. Qed.

Lemma splitC A B C
      {eA : equiv A} {eB : equiv B} {eC : equiv C}
      (f1 f2 : B ~> C) (g1 g2 : A ~> B)
  : f1 =e f2 -> g1 =e g2 -> f1 \o g1 =e f2 \o g2.
Proof. intros ->->. reflexivity. Qed.

Lemma hylo_fusion_l `{F : Container Sh P} A B C
      {eA : equiv A} {eB : equiv B} {eC : equiv C}
      (h1 : RCoalg F A) (g1 : Alg F B) (g2 : Alg F C) (f2 : B ~> C)
      (E2 : f2 \o g1 =e g2 \o fmap f2)
  : f2 \o hylo g1 h1 =e hylo g2 h1.
Proof.
  rewrite hylo_univ.
  rewrite fmap_comp.
  rewrite compA.
  rewrite <- E2.
  rewrite <- compA.
  rewrite <- compA.
  rewrite (compA g1).
  rewrite <- hylo_unr.
  reflexivity.
Qed.

Lemma hylo_fusion_r `{F : Container Sh P} A B C
      {eA : equiv A} {eB : equiv B} {eC : equiv C}
      (h1 : RCoalg F B) (g1 : Alg F C) (h2 : RCoalg F A)
      (f1 : A ~> B) (E1 : h1 \o f1 =e fmap f1 \o h2)
  : hylo g1 h1 \o f1 =e hylo g1 h2.
Proof.
  rewrite hylo_univ.
  rewrite fmap_comp.
  rewrite <- compA.
  rewrite <- compA.
  rewrite <- E1.
  rewrite compA.
  rewrite compA.
  rewrite <- hylo_unr.
  reflexivity.
Qed.

Lemma deforest `{F : Container Sh P} A B C
      {eA : equiv A} {eB : equiv B} {eC : equiv C}
      (h1 : RCoalg F A) (g1 : Alg F B) (h2 : RCoalg F B) (g2 : Alg F C)
      (INV: h2 \o g1 =e id)
  : hylo g2 h2 \o hylo g1 h1 =e hylo g2 h1.
Proof.
  apply hylo_fusion_l.
  rewrite hylo_unr at 1.
  rewrite <- compA.
  rewrite INV.
  rewrite idKr.
  reflexivity.
  Restart.
  apply hylo_fusion_r.
  rewrite hylo_unr at 1.
  rewrite compA,compA.
  rewrite INV.
  rewrite idKl.
  reflexivity.
Qed.

Corollary cata_ana_hylo `(F : Container Sh P)
          A B {eA : equiv A} {eB : equiv B}
          (g : Alg F B) (h : RCoalg F A)
  : cata g \o rana h =e hylo g h.
Proof. rewrite hylo_cata,hylo_ana. apply deforest, l_out_in. Qed.
