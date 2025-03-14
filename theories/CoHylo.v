Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import HYLO.Equivalence.
Require Import HYLO.Morphism.
Require Import HYLO.Container.
Require Import HYLO.Algebra.
Require Import HYLO.Coalgebra.
Require Import HYLO.FCoalgebra.

CoInductive GFix `(F : Cont Sh Po)
  := OutOp { out_shape : Sh;
             out_cont  : Pos out_shape -> GFix F
           }.

Section HyloDef.
  Context `{F : Cont Sf Pf} `{G : Cont Sg Pg} `{eA : setoid A}.

  Definition stream_gen := nat -> nat * nat.

  CoInductive strm := ConsS (n : nat) (t : strm).

  CoFixpoint gen (l : stream_gen) (i : nat) : strm :=
    ConsS (fst (l i)) (gen l (snd (l i))).

  Definition fmap (f : nat -> nat) := fun xm => (f (fst xm), snd xm).

  Definition nats_coalg x := (x, S x).

  Fixpoint nats x :=
    match x with
    | 0 => (0, 1)
    | S n => fmap (fun x => x + 1) (nats n)
    end.

  Definition nats_alg c x :=
    match c x with
    | (n , m) =>


  hylo: (c : nat -> (nat, nat) -> F A) (a : )

  (* Like a "hylo one level up?"
   *)

  (* The algebra should build on the coalgebra somehow (e.g. "nats is recursive
  on the input to the coalgebra"?)*)

  (* The hylo for "nats" should build a coalgebra!!!
   * The corec-hylo is simply a [gen (co_hylo a c)] *)
  (* But what is a coalgebra in this setting then?
   *)


  CoFixpoint nats n :=
    match n with
    | Cons n t => Cons n (nats (Cons n (nats (Cons (S n) t))))
    end.

  (* NOTES:
     - [a] needs to expand *STATICALLY* to a sequence of constructor/match/fun expressions
  *)
  Set Printing Coercions.
  Definition hylo_def (a : App F (GFix G) -> GFix G) (c : A -> App F A)
    : forall (x : A + App F (GFix G)), GFix G :=
    cofix f x :=
      match x with
      | inl x => inr (match c x with
                         | MkCont sx cx => MkCont sx (fun e => f (inl (cx e)))
                         end)
      | inr x => a x
      end.
      match c x with
      | MkCont sx cx =>
          a (MkCont sx (fun e => f (cx e)))
      end.
  Arguments hylo_def a c x H : clear implicits.

  Definition hylo_def (a : Alg F B) (c : Coalg F A)
    : forall (x : A), RecF c x -> B :=
    fix f x H :=
      match c x as cx
            return (forall e : Pos (shape cx), RecF c (cont cx e)) -> B
      with
      | MkCont sx cx => fun H => a (MkCont sx (fun e => let ce := cx e in f ce (H e)))
      end (RecF_inv H).
  Arguments hylo_def a c x H : clear implicits.

  Lemma hylo_def_irr (g : Alg F B) (h : Coalg F A)
    : forall (x : A) (F1 F2 : RecF h x), hylo_def g h x F1 =e hylo_def g h x F2.
  Proof.
    fix Ih 2. intros x0 [x Fx] F2. clear x0. destruct F2 as [x Fy]. simpl.
    generalize dependent (h x).  clear x. intros [s_x c_x] Fx Fy. simpl in *.
    apply app_eq. split; [reflexivity|intros d1 d2 e].
    rewrite (elem_val_eq e). simpl in *. apply Ih. Guarded.
  Qed.

  Definition hylo_f__ (g : Alg F B) (h : RCoalg F A)
    := Eval unfold hylo_def in fun x => hylo_def g h x (terminating h x).

  Lemma hylo_f___arr (a0 a1 : Alg F B) (c0 c1 : RCoalg F A)
    (Ea : a0 =e a1) (Ec : c0 =e c1)
    : forall x y, x =e y -> hylo_f__ a0 c0 x =e hylo_f__ a1 c1 y.
  Proof.
    unfold hylo_f__.
    intros x y. generalize (terminating c0 x),(terminating c1 y). revert x y.
    fix Ih 3. intros x y Fx Fy H. destruct Fx as [x Fx], Fy as [y Fy].
    simpl. assert (Cxy : c0 x =e c1 y) by (rewrite H; apply Ec).
    destruct (c0 x) as [sx kx], (c1 y) as [sy ky]. simpl in *.
    destruct Cxy as [Sxy Kxy]. simpl in Sxy, Kxy.
    rewrite Ea. apply app_eq. split; simpl; auto.
  Qed.

  Definition hylo_f_ (g : Alg F B) (h : RCoalg F A)
    : A ~> B := Eval unfold hylo_f__ in
      MkMorph (hylo_f___arr (e_refl g) (e_refl h)).

  Lemma hylo_f__arr (a : Alg F B)
    : forall x y, x =e y -> hylo_f_ a x =e hylo_f_ a y.
  Proof. intros x y h v. apply hylo_f___arr; auto with ffix. Qed.

  Definition hylo_f (g : Alg F B)
    : RCoalg F A ~> A ~> B :=
    Eval unfold hylo_f_ in MkMorph (hylo_f__arr g).

  Lemma hylo_f_arr : forall x y, x =e y -> hylo_f x =e hylo_f y.
  Proof. intros x y E h v. apply hylo_f___arr; auto with ffix. Qed.

  Definition hylo : Alg F B ~> RCoalg F A ~> A ~> B :=
    Eval unfold hylo_f in MkMorph hylo_f_arr.

  Lemma hylo_univ_r (g : Alg F B) (h : RCoalg F A) (f : A ~> B)
    : f =e g \o fmap f \o h -> f =e hylo g h.
  Proof.
    intros H x. simpl.  unfold hylo_f__.
    generalize (terminating h x). revert x.
    fix Ih 2. intros x Fx. rewrite (H _). simpl. unfold comp. unfold fmap.
    destruct Fx as [x Fx]. simpl. destruct (h x) as [s_x c_x]. simpl in *.
    apply app_eq. simpl. split; [reflexivity|simpl; intros d1 d2 e].
    rewrite (elem_val_eq e). apply Ih. Guarded.
  Qed.

  Lemma hylo_univ_l (g : Alg F B) (h : RCoalg F A) (f : A ~> B)
    : f =e hylo g h -> f =e g \o fmap f \o h.
  Proof.
    intros H. rewrite H. clear H f. simpl. intros x. unfold hylo_f__.
    destruct (terminating h x) as [x Fx]. simpl.
    destruct (h x) as [s_x c_x]. simpl in *.
    apply app_eq. split; [reflexivity|simpl; intros d1 d2 e].
    rewrite (elem_val_eq e). apply hylo_def_irr.
  Qed.

  Lemma hylo_univ (g : Alg F B) (h : RCoalg F A) (f : A ~> B)
    : f =e hylo g h <-> f =e g \o fmap f \o h.
  Proof. split;[apply hylo_univ_l|apply hylo_univ_r]. Qed.

  Corollary hylo_unr (g : Alg F B) (h : RCoalg F A)
    : hylo g h =e g \o fmap (hylo g h) \o h.
  Proof. rewrite <-hylo_univ. reflexivity. Qed.

End HyloDef.

Section HyloFusion.
  Context `{F : Cont Sh Po}.
  Context `{eA : setoid A} `{eB : setoid B} `{eC : setoid C}.

  Lemma hylo_cata (g : Alg F B) : cata g =e hylo g l_out.
  Proof. rewrite hylo_univ. rewrite<-cata_univ. reflexivity. Qed.

  Lemma hylo_ana (h : RCoalg F A) : rana h =e hylo l_in h.
  Proof. rewrite hylo_univ. rewrite <-rana_univ. reflexivity. Qed.

  Lemma splitC (f1 f2 : B ~> C) (g1 g2 : A ~> B)
    : f1 =e f2 -> g1 =e g2 -> f1 \o g1 =e f2 \o g2.
  Proof. intros ->->. reflexivity. Qed.

  Lemma hylo_fusion_l (h1 : RCoalg F A) (g1 : Alg F B) (g2 : Alg F C)
    (f2 : B ~> C) (E2 : f2 \o g1 =e g2 \o fmap f2)
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

  Lemma hylo_fusion_r (h1 : RCoalg F B) (g1 : Alg F C) (h2 : RCoalg F A)
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

  Lemma deforest (h1 : RCoalg F A) (g2 : Alg F C)
    (g1 : Alg F B) (h2 : RCoalg F B) (INV: h2 \o g1 =e id)
    : hylo g2 h2 \o hylo g1 h1 =e hylo g2 h1.
  Proof.
    apply hylo_fusion_l.
    rewrite hylo_unr at 1.
    rewrite <- compA.
    rewrite INV.
    rewrite idKr.
    reflexivity.
    (* Restart. *)
    (* apply hylo_fusion_r. *)
    (* rewrite hylo_unr at 1. *)
    (* rewrite compA,compA. *)
    (* rewrite INV. *)
    (* rewrite idKl. *)
    (* reflexivity. *)
  Qed.
End HyloFusion.

Corollary cata_ana_hylo `(F : Cont Sh P) `{setoid A} `{setoid B}
  (g : Alg F B) (h : RCoalg F A)
  : cata g \o rana h =e hylo g h.
Proof. rewrite hylo_cata,hylo_ana. apply deforest, l_out_in. Qed.

Corollary cata_ana_hylo_f `(F : Cont Sh P) `{setoid A} `{setoid B}
  (g : Alg F B) (h : RCoalg F A)
  : cata g \o ccata l_in \o liftP (ana h) (rcoalg_fin h) =e hylo g h.
Proof. rewrite <- compA, ana_rana, cata_ana_hylo. reflexivity. Qed.

Corollary cata_ana_hylo_gf `(F : Cont Sh P) `{setoid A} `{setoid B}
  (g : Alg F B) (h : RCoalg F A)
  : ccata g \o liftP (ana h) (rcoalg_fin h) =e hylo g h.
Proof. rewrite <- cata_ccata, cata_ana_hylo_f. reflexivity. Qed.

Corollary hylo_map_shift `{F : Cont Sf P} `{setoid Sg} {G : Cont Sg P}
  `{setoid A} `{setoid B}
  (g : Alg G B) (m : naturalM F G) (h : RCoalg F A)
  : hylo (g \o natural m) h =e hylo g (natural m \o h).
Proof.
  apply hylo_univ. rewrite hylo_unr at 1.
  rewrite (compA _ (natural m) h), <- (compA g _ (natural m)).
  unfold natural. rewrite <- eta_is_natural, compA.
  reflexivity.
Qed.

Arguments deforest & {_ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Arguments l_out_in & {_ _ _ F}.

Corollary hylo_map_fusion_c `{F : Cont Sf P} `{setoid Sg} {G : Cont Sg P}
  `{setoid A} `{setoid B} (g : Alg G B) (m : naturalM F G) (h : RCoalg F A)
  : hylo g l_out \o hylo (l_in \o natural m) h =e hylo g (natural m \o h).
Proof.
  rewrite hylo_map_shift, deforest; try reflexivity.
  apply l_out_in.
Qed.

Corollary hylo_map_fusion `{F : Cont Sf P} `{setoid Sg} {G : Cont Sg P}
  `{setoid A} `{setoid B}
  (g : Alg G B) (m : naturalM F G) (h : RCoalg F A)
  : hylo g l_out \o hylo (l_in \o natural m) h =e hylo (g \o natural m) h.
Proof.
  rewrite hylo_map_shift, deforest, ?hylo_map_shift.
  reflexivity.
  apply l_out_in.
Qed.

Definition everywhere `{F : Cont Sf P} `{setoid Sg} {G : Cont Sg P}
  (f : naturalM F G) : LFix F ~> LFix G :=
  hylo (l_in \o natural f) l_out.
  (* papp hylo l_out \o eapp \o pair (const (comp l_in)) natural. *)

(* Lemma app_everywhere  *)
(*   `{F : Cont Sh Pf} {Pg} {G : Cont Sh Pg} (f : X ~> Y) *)
(*   : everywhere f = hylo (l_in \o cmap f) l_out. *)
(* Proof. trivial. Qed. *)

Lemma everywhere_id `{F : Cont Sf P} :
  everywhere id =e id (A:=LFix F).
Proof.
  unfold everywhere. symmetry. apply hylo_univ.
  rewrite fmap_id, idKr, natural_idI, idKr, l_in_out.
  reflexivity.
Qed.

Lemma everywhere_comp `{F : Cont Sf P} `{SSg : setoid Sg} {G : Cont Sg P}
  `{SSh : setoid Sh} {H : Cont Sh P} (f : naturalM G H) (g : naturalM F G)
  : everywhere f \o everywhere g =e everywhere (f \o g).
Proof.
  unfold everywhere. rewrite hylo_map_fusion, <- compA.
  rewrite natural_comp. reflexivity.
Qed.
