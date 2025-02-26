Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import HYLO.Equivalence.
Require Import HYLO.Morphism.
Require Import HYLO.Container.

Definition Alg `{F : Container Sh P} A {eA : equiv A} := App F A ~> A.
Arguments Alg {Sh}%_type_scope {Esh} {P}%_type_scope F A {eA}.

Unset Elimination Schemes.
Inductive LFix `(F : Container Sh P) : Type :=
  LFix_in { LFix_out : App F (LFix F) }.
Set Elimination Schemes.
Arguments LFix {Sh}%_type_scope {Esh} {P}%_type_scope F.

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

Section Polynomials.
  Inductive Id_ : Type := MkId.

  Instance Id : Container Id_ unit :=
    { dom := const true
    }.

  (* Would be nice to have these kinds of isomorphisms between types/Container
   * applications, and somehow "automate" their use interchangeably ...
   * It is annoying not having "App Id A = A", but otherwise it'd be hard taking
   * fixpoints, etc
   *)
  Definition from_id A {eA : equiv A} : App Id A ~> A.
    refine {|
        app := fun x : App Id A => cont x (MkElem tt eq_refl);
        f_eq := _
      |}.
    intros [[] xk] [[] yk] []; auto with ffix.
  Defined.

  Definition to_id A {eA : equiv A} : A ~> App Id A.
    refine {|
        app := fun x : A => MkCont MkId (fun _ => x);
        f_eq := _
      |}.
    intros x y H; simpl; auto with ffix.
  Defined.

  Lemma id_cancel_l `{eA : equiv A} : from_id \o to_id =e id (A:=A).
  Proof. intros x. reflexivity. Qed.

  Lemma id_cancel_r `{eA : equiv A} : to_id \o from_id =e id (A:=App Id A).
  Proof.
    intros [[] h]. simpl. unfold comp, Datatypes.id. simpl.
    split.
    - reflexivity.
    - simpl. intros [[] d1] [[] d2]. simpl.
      rewrite (bool_irrelevance d2 eq_refl). reflexivity.
  Qed.

  Definition tconst `{equiv A} `{equiv B} (x : B) : A ~> B.
    refine {| app := fun _ => x |}.
    reflexivity.
  Qed.

  Inductive K_ (A : Type) := MkK (const : A).

  Inductive void : Set :=.

  (* Instance K A : Container (K_ A) void := *)
  (*   { dom := fun _ f => match f with end *)
  (*   }. *)
  (* (* Pairs *) *)

  (* Instance Prod `{Container Sf Pf} `{Container Sg Pg} *)
  (*   : Container (Sf * Sg) (Pf + Pg) := *)
  (*   { dom := fun sh p => *)
  (*              match p with *)
  (*              | inl pf => dom (fst sh) pf *)
  (*              | inr pg => dom (snd sh) pg *)
  (*              end *)
  (*   }. *)
  (* Arguments Prod {Sf Pf} F {Sg Pg} G : rename. *)

  (* Definition einl *)
  (*   `{F : Container Sf Pf} `{G : Container Sg Pg} (sh : Sf * Sg) *)
  (*   (k : Pos (fst sh)) : Pos sh := *)
  (*   MkElem (inl (val k)) (InDom k). *)
  (* Arguments einl & {Sf Pf F Sg Pg G sh}. *)

  (* Definition einr *)
  (*   `{F : Container Sf Pf} `{G : Container Sg Pg} (sh : Sf * Sg) *)
  (*   (k : Pos (snd sh)) : Pos sh := *)
  (*   MkElem (F := Prod F G) *)
  (*     (inr (val k)) (InDom k : dom sh (inr (val k)) = true). *)
  (* Arguments einr & {Sf Pf F Sg Pg G sh}. *)

  (* Definition ecase `{F : Container Sf Pf} `{G : Container Sg Pg} *)
  (*   (sf : Sf) (sg : Sg) (k : Pos (F := Prod F G) (sf, sg)) *)
  (*   : Pos sf + Pos sg := *)
  (*   match val k as pos *)
  (*         return dom (sf, sg) pos = true -> Pos sf + Pos sg *)
  (*   with *)
  (*      | inl x => fun p => inl (MkElem x p) *)
  (*      | inr x => fun p => inr (MkElem x p) *)
  (*      end (InDom k). *)
  (* Arguments ecase {Sf Pf F Sg Pg G sf sg}. *)

  (* Definition fproj1 `{equiv X} `{F : Container Sf Pf} `{G : Container Sg Pg} *)
  (*   : App (Prod F G) X ~> App F X. *)
  (*   refine {| app := fun p : App (Prod F G) X => *)
  (*                      MkCont (fst (shape p)) (fun x => cont p (einl x)); *)
  (*            f_eq := _ *)
  (*          |}. *)
  (*   intros [x1 x2] [y1 y2] HEq. simpl in *. *)
  (*   destruct HEq. simpl in *. subst. constructor; simpl in *; auto. *)
  (*   intros e d1 d2. simpl. apply Ek. *)
  (* Defined. *)

  (* Definition fproj2 `{equiv X} `{F : Container Sf Pf} `{G : Container Sg Pg} *)
  (*   : App (Prod F G) X ~> App G X. *)
  (*   refine {| app := fun p : App (Prod F G) X => *)
  (*                      MkCont (snd (shape p)) (fun x => cont p (einr x)); *)
  (*            f_eq := _ *)
  (*          |}. *)
  (*   intros [x1 x2] [y1 y2] HEq. simpl. *)
  (*   destruct HEq. simpl in *. subst. constructor; simpl in *; auto. *)
  (*   intros e d1 d2. apply Ek. *)
  (* Defined. *)

  (* Definition fpair `{equiv X} `{F : Container Sf Pf} `{G : Container Sg Pg} *)
  (*   `{equiv A} (f : A ~> App F X) (g : A ~> App G X) : A ~> App (Prod F G) X. *)
  (*   refine {| *)
  (*       app := fun x => *)
  (*                let fx := f x in *)
  (*                let gx := g x in *)
  (*                MkCont (shape fx, shape gx) *)
  (*                  (fun p => *)
  (*                     match ecase p with *)
  (*                     | inl p => cont fx p *)
  (*                     | inr p => cont gx p *)
  (*                     end); *)
  (*     |}. *)
  (*   intros x y Eq. simpl in *. *)
  (*   destruct (f_eq f Eq) as [Hs1 Hk1], (f_eq g Eq) as [Hs2 Hk2]. *)
  (*   constructor; simpl. *)
  (*   - rewrite Hs1, Hs2. reflexivity. *)
  (*   - intros [p|p] d1 d2; simpl. *)
  (*     * rewrite Hk1.  reflexivity. *)
  (*     * rewrite Hk2.  reflexivity. *)
  (* Defined. *)

  (* Instance Sum `{Container Sf Pf} `{Container Sg Pg} *)
  (*   : Container (Sf + Sg) (Pf + Pg) := *)
  (*   { dom := fun sh p => *)
  (*              match sh, p with *)
  (*              | inl sf, inl pf => dom sf pf *)
  (*              | inr sg, inr pg => dom sg pg *)
  (*              | _, _ => false *)
  (*              end *)
  (*   }. *)
  (* Arguments Sum {Sf Pf} F {Sg Pg} G : rename. *)

  (* Lemma false_not_true : false = true -> False. *)
  (* Proof. discriminate. Qed. *)


  (* Definition un_inl `{F : Container Sf Pf} `{G : Container Sg Pg} {sh : Sf} *)
  (*   (p : Pos (F := Sum F G) (inl sh)) : Pos sh := *)
  (*   let (pfg, Hdom) := p in *)
  (*   match pfg return dom (inl sh) pfg = true -> _ with *)
  (*   | inl pf => fun H => MkElem pf H *)
  (*   | inr pf => fun Hdom => match false_not_true Hdom with end *)
  (*   end Hdom. *)

  (* Definition in_inl `{F : Container Sf Pf} `{G : Container Sg Pg} {sh : Sf} *)
  (*   (p : Pos (F := F) sh) : Pos (F := Sum F G) (inl sh) := *)
  (*   let (p, Hp) := p in MkElem (inl p) (Hp : dom (inl sh) (inl p) = true). *)

  (* Definition un_inr `{F : Container Sf Pf} `{G : Container Sg Pg} {sh : Sg} *)
  (*   (p : Pos (F := Sum F G) (inr sh)) : Pos sh := *)
  (*   let (pfg, Hdom) := p in *)
  (*   match pfg return dom (inr sh) pfg = true -> _ with *)
  (*   | inr pf => fun H => MkElem pf H *)
  (*   | inl pf => fun Hdom => match false_not_true Hdom with end *)
  (*   end Hdom. *)

  (* Definition in_inr `{F : Container Sf Pf} `{G : Container Sg Pg} {sh : Sg} *)
  (*   (p : Pos (F := G) sh) : Pos (F := Sum F G) (inr sh) := *)
  (*   let (p, Hp) := p in *)
  (*   MkElem (inr p) (Hp : dom (Container := Sum F G) (inr sh) (inr p) = true). *)

  (* Definition finj1 `{equiv X} `{F : Container Sf Pf} `{G : Container Sg Pg} *)
  (*   : App F X ~> App (Sum F G) X. *)
  (*   refine {| *)
  (*     app := *)
  (*         fun x => *)
  (*           MkCont (inl (shape x)) *)
  (*             (fun p => *)
  (*                cont x (un_inl p) *)
  (*             ) *)
  (*     |}. *)
  (*   intros [sx kx] [sy ky]; simpl. *)
  (*   intros [Seq Keq]; simpl in *. *)
  (*   constructor; simpl in *. *)
  (*   - rewrite Seq. reflexivity. *)
  (*   - intros [p|p] d1 d2; simpl. *)
  (*     * apply Keq. *)
  (*     * discriminate. *)
  (* Defined. *)

  (* Definition finj2 `{equiv X} `{F : Container Sf Pf} `{G : Container Sg Pg} *)
  (*   : App G X ~> App (Sum F G) X. *)
  (*   refine {| *)
  (*     app := *)
  (*         fun x : App G X => *)
  (*           MkCont (inr (shape x)) *)
  (*             (fun p => *)
  (*                cont x (un_inr p) *)
  (*             ) *)
  (*     |}. *)
  (*   intros [sx kx] [sy ky]; simpl. *)
  (*   intros [Seq Keq]; simpl in *. *)
  (*   constructor; simpl in *. *)
  (*   - rewrite Seq. reflexivity. *)
  (*   - intros [p|p] d1 d2; simpl. *)
  (*     * discriminate. *)
  (*     * apply Keq. *)
  (* Defined. *)

  (* Definition fcase `{equiv X} `{equiv A} *)
  (*   `{F : Container Sf Pf} `{G : Container Sg Pg} *)
  (*   (f : App F X ~> A) (g : App G X ~> A) *)
  (*   : App (Sum F G) X ~> A. *)
  (*   refine {| *)
  (*       app := fun fgx : App (Sum F G) X => *)
  (*                let (sh, k) := fgx in *)
  (*                match sh return (Pos sh -> X) -> A with *)
  (*                | inl sh => fun k => f (MkCont sh (fun p => k (in_inl p))) *)
  (*                | inr sh => fun k => g (MkCont sh (fun p => k (in_inr p))) *)
  (*                end k *)
  (*     |}. *)
  (*   intros [sx kx] [sy ky] [Esh Ek]. simpl in Esh. revert kx Ek. *)
  (*   rewrite Esh. clear Esh sx. intros kx Ek. *)
  (*   destruct sy as [sy|sy]; apply f_eq; constructor; simpl in *; auto. *)
  (* Defined. *)
End Polynomials.

(* Arguments Sum {Sf Pf} F {Sg Pg} G : rename. *)
(* Arguments Prod {Sf Pf} F {Sg Pg} G : rename. *)

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
  destruct y as [sy ky]; simpl.
  destruct z as [sz kz]; simpl.
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
  {| app := _; f_eq := l_in_eq (F:=F) |}.
Definition l_out `{F : Container Sh P} : CoAlg F (LFix F) :=
  {| app := _; f_eq := l_out_eq (F:=F) |}.

Lemma l_in_out `(F : Container Sh P) : l_in \o l_out =e id (A:=LFix F).
Proof.
  simpl. intros. split; try reflexivity. intros e1 e2 He.
  rewrite (elem_val_eq He). apply LFixR_refl.
Qed.

Lemma l_out_in `(F : Container Sh P)
  : l_out \o l_in =e id (A:=App F (LFix F)).
Proof.
  simpl. intros. split; try reflexivity. intros e1 e2 He.
  rewrite (elem_val_eq He). apply LFixR_refl.
Qed.

(* Definition what_was_the_name_f S P {F : Container S P} `{equiv A} `{equiv B} *)
(*   (g : App (Prod F (K B)) A ~> A) *)
(*   : LFix F -> B -> A. *)
(*   refine (fix f x b := *)
(*        match x with *)
(*        | LFix_in k => g (MkCont _ _) *)
(*        end). *)
(*   About LFix_in. *)

Definition cata_f `{F : Container Sh P} A {eA : equiv A} (g : Alg F A)
  : LFix F -> A
  := fix f x := g (fmapA (F:=F) f (LFix_out (F:=F) x)).
Arguments cata_f {Sh Esh P F A eA} g.

Lemma cata_arr `{F : Container Sh P} A {eA : equiv A} (g : Alg F A)
  : forall x y, x =e y -> cata_f g x =e cata_f g y.
Proof.
  induction x as [sx Ih]. intros [sy]. simpl in *. intros [Es Ek].
  apply (f_eq g). split; [trivial|intros e1 e2 Hv]. apply Ih. auto.
Qed.

Definition cata `{F : Container Sh P} A {eA : equiv A} (g : Alg F A)
  : LFix F ~> A
  := {| app := fix f x :=
           g ((fun x => MkCont (F:=F) (shape x)
                          (fun e => f (cont x e))) (LFix_out (F:=F) x));
       f_eq := cata_arr g |}.
Arguments cata {Sh}%_type_scope {Esh} {P}%_type_scope {F} [A]%_type_scope {eA} g.

Lemma cata_univ_r `{F : Container Sh P} `{eA : equiv A} (g : Alg F A)
      (f : LFix F ~> A)
  : f =e g \o fmap f \o l_out -> f =e cata g.
Proof.
  intros H e. induction e as [e Ih]. simpl in *. rewrite H. apply f_eq.
  split; try auto with ffix. simpl in *. intros e1 e2 Hv. rewrite Ih.
  rewrite (elem_val_eq Hv). reflexivity.
Qed.

Lemma cata_univ_l `{F : Container Sh P} `{eA : equiv A} (g : Alg F A)
      (f : LFix F ~> A)
  : f =e cata g -> f =e g \o fmap f \o l_out.
Proof.
  intros H [e]. simpl in *. rewrite H. apply f_eq. simpl.
  split; auto with ffix. simpl. intros e1 e2 Hv. rewrite H.
  rewrite (elem_val_eq Hv). reflexivity.
Qed.

Lemma cata_univ `{F : Container Sh P} `{eA : equiv A} (g : Alg F A)
      (f : LFix F ~> A)
  : f =e cata g <-> f =e g \o fmap f \o l_out.
Proof. split;[apply cata_univ_l|apply cata_univ_r]. Qed.

(* Finite anamorphisms *)
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
  - destruct (f_eq h Hxy). auto.
  - intros e d1 d2. simpl. apply Ih. Guarded.
    destruct (f_eq h Hxy). auto.
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
       f_eq := ana_arr h
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

(** Hylomorphisms **)

Definition hylo_f_ `{F : Container Sh P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg F B) (h : CoAlg F A)
  : forall (x : A), FinF h x -> B
  := fix f x H :=
       match h x as h0
             return
             (forall e : Pos (shape h0), FinF h (cont h0 e)) ->
             B
       with
       | MkCont s_x c_x => fun H => g (MkCont s_x (fun e => f (c_x e) (H e)))
       end (FinF_inv H).

Lemma hylo_f_irr `{F : Container Sh P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg F B) (h : CoAlg F A)
  : forall (x : A) (F1 F2 : FinF h x), hylo_f_ g F1 =e hylo_f_ g F2.
Proof.
  fix Ih 2. intros x0 [x Fx] F2. clear x0. destruct F2 as [x Fy]. simpl.
  generalize dependent (h x).  clear x. intros [s_x c_x] Fx Fy. simpl in *.
  apply f_eq. split; [reflexivity|intros d1 d2 e].
  rewrite (elem_val_eq e). simpl in *. apply Ih. Guarded.
Qed.

Definition hylo_f `{F : Container Sh P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg F B) (h : FCoAlg F A)
  := fun x => hylo_f_ g (finite h x).

Lemma hylo_arr `{F : Container Sh P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg F B) (h : FCoAlg F A)
  : forall x y, x =e y -> hylo_f g h x =e hylo_f g h y.
Proof.
  unfold hylo_f.
  intros x y. generalize x,y,(finite h x),(finite h y). clear x y.
  fix Ih 3. intros x y [x' Fx] [y' Fy] H. simpl.
  generalize (@f_eq _ _ _ _ h _ _ H). revert Fx Fy.
  generalize (h x') (h y'). intros [s_x c_x] [s_y c_y]. simpl.
  intros Fx Fy [Exy Ec]. simpl in *.
  apply f_eq. split; [trivial|simpl; intros d1 d2 e].
  apply Ih. Guarded. apply Ec, e.
Qed.

Definition hylo `{F : Container Sh P}
           A B {eA : equiv A} {eB : equiv B}
           (g : Alg F B) (h : FCoAlg F A)
  : A ~> B
  := {| app :=
         fun x =>
           (fix f x H :=
              match h x as h0
                    return
                    (forall e : Pos (shape h0), FinF h (cont h0 e)) ->
                    B
              with
              | MkCont s_x c_x =>
                  fun H => g (MkCont s_x (fun e => f (c_x e) (H e)))
              end (FinF_inv H)) x (finite h x);
       f_eq := hylo_arr g h |}.

(* "universal" (quotes) because these are *finite* hylos, otherwise this
   direction would not work
 *)
Lemma hylo_univ_r `{F : Container Sh P}
      A B {eA : equiv A} {eB : equiv B}
      (g : Alg F B) (h : FCoAlg F A) (f : A ~> B)
  : f =e g \o fmap f \o h -> f =e hylo g h.
Proof.
  intros H. unfold hylo, hylo_f. simpl.
  intros x. generalize x, (finite h x). clear x.
  fix Ih 2. intros x Fx. rewrite (H _). simpl. unfold comp. unfold fmap.
  destruct Fx as [x Fx]. simpl. destruct (h x) as [s_x c_x]. simpl in *.
  apply f_eq. simpl. split; [reflexivity|simpl; intros d1 d2 e].
  rewrite (elem_val_eq e). apply Ih. Guarded.
Qed.

Lemma hylo_univ_l `{F : Container Sh P}
      A B {eA : equiv A} {eB : equiv B}
      (g : Alg F B) (h : FCoAlg F A) (f : A ~> B)
  : f =e hylo g h -> f =e g \o fmap f \o h.
Proof.
  intros H. rewrite H. clear H f. simpl. intros x.
  destruct (finite h x) as [x Fx]. simpl.
  destruct (h x) as [s_x c_x]. simpl in *.
  apply f_eq. split; [reflexivity|simpl; intros d1 d2 e].
  rewrite (elem_val_eq e). apply hylo_f_irr.
Qed.

Lemma hylo_univ `{F : Container Sh P}
      A B {eA : equiv A} {eB : equiv B}
      (g : Alg F B) (h : FCoAlg F A) (f : A ~> B)
  : f =e hylo g h <-> f =e g \o fmap f \o h.
Proof. split;[apply hylo_univ_l|apply hylo_univ_r]. Qed.

Corollary hylo_unr `{F : Container Sh P}
      A B {eA : equiv A} {eB : equiv B}
      (g : Alg F B) (h : FCoAlg F A)
  : hylo g h =e g \o fmap (hylo g h) \o h.
Proof. rewrite <-hylo_univ. reflexivity. Qed.

Lemma fin_out `(F : Container Sh P) : forall x, FinF (F:=F) l_out x.
Proof. induction x as [s Ih]. constructor. apply Ih. Qed.

Definition f_out `(F : Container Sh P) : FCoAlg F (LFix F) :=
  exist _ _ (fin_out (F:=F)).
Arguments f_out & {Sh}%_type_scope {Esh} {P}%_type_scope {F}.

Lemma hylo_cata `{F : Container Sh P} B {eB : equiv B} (g : Alg F B)
  : cata g =e hylo g f_out.
Proof. rewrite hylo_univ. apply cata_univ. reflexivity. Qed.

Lemma hylo_ana `{F : Container Sh P} A {eA : equiv A} (h : FCoAlg F A)
  : ana h =e hylo l_in h.
Proof. rewrite hylo_univ. apply ana_univ. reflexivity. Qed.

Lemma compA A B C D {eA : equiv A} {eB : equiv B}
      {eC : equiv C} {eD : equiv D}
      (f : C ~> D) (g : B ~> C) (h : A ~> B)
  : f \o (g \o h) =e (f \o g) \o h.
Proof. intros x. auto with ffix. Qed.

Lemma idKl A B {eA : equiv A} {eB : equiv B} (f : A ~> B)
  : f \o id =e f.
Proof. intros x. eauto with ffix. Qed.

Lemma idKr A B {eA : equiv A} {eB : equiv B} (f : A ~> B)
  : id \o f =e f.
Proof. intros x. eauto with ffix. Qed.

Lemma splitC A B C
      {eA : equiv A} {eB : equiv B} {eC : equiv C}
      (f1 f2 : B ~> C) (g1 g2 : A ~> B)
  : f1 =e f2 -> g1 =e g2 -> f1 \o g1 =e f2 \o g2.
Proof. intros ->->. reflexivity. Qed.

Lemma hylo_fusion_l `{F : Container Sh P} A B C
      {eA : equiv A} {eB : equiv B} {eC : equiv C}
      (h1 : FCoAlg F A) (g1 : Alg F B) (g2 : Alg F C) (f2 : B ~> C)
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
      (h1 : FCoAlg F B) (g1 : Alg F C) (h2 : FCoAlg F A)
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
      (h1 : FCoAlg F A) (g1 : Alg F B) (h2 : FCoAlg F B) (g2 : Alg F C)
      (INV: h2 \o g1 =e id)
  : hylo g2 h2 \o hylo g1 h1 =e hylo g2 h1.
Proof.
  apply hylo_fusion_l.
  rewrite hylo_unr at 1.
  rewrite <- compA.
  rewrite INV.
  rewrite idKl.
  reflexivity.
  Restart.
  apply hylo_fusion_r.
  rewrite hylo_unr at 1.
  rewrite compA,compA.
  rewrite INV.
  rewrite idKr.
  reflexivity.
Qed.

Corollary cata_ana_hylo `(F : Container Sh P)
          A B {eA : equiv A} {eB : equiv B}
          (g : Alg F B) (h : FCoAlg F A)
  : cata g \o ana h =e hylo g h.
Proof. rewrite hylo_cata,hylo_ana. apply deforest,l_out_in. Qed.

(* Section Sums. *)
(*   Definition inj1 `{eA : equiv A} `{eB : equiv B} : A ~> A + B. *)
(*     refine {| app := fun p => inl p; *)
(*              f_eq := _ *)
(*            |}. *)
(*     auto. *)
(*   Defined. *)

(*   Definition inj2 `{eA : equiv A} `{eB : equiv B} : B ~> A + B. *)
(*     refine {| app := fun p => inr p; *)
(*              f_eq := _ *)
(*            |}. *)
(*     auto. *)
(*   Defined. *)

(*   Definition tcase `{eA : equiv A} `{eB : equiv B} `{eC : equiv C} *)
(*     (f : A ~> C) (g : B ~> C) : A + B ~> C. *)
(*     refine {| app := fun p => *)
(*                        match p with *)
(*                        | inr p => g p *)
(*                        | inl p => f p *)
(*                        end; *)
(*              f_eq := _ *)
(*            |}. *)
(*     intros [x|x] [y|y]; simpl; try apply f_eq; try intros []. *)
(*   Defined. *)
(* End Sums. *)

Require List.
Section ExQsort.

  (* Defining a tree *)

  (* shapes *)
  Inductive Ts A := | Leaf | Node (ELEM : A).
  Inductive Tp := | Lbranch | Rbranch. (* positions *)
  (* position valid in shape? *)
  Definition t_dom A : Ts A * Tp ~> bool.
    refine {| app := fun x =>
                   match x with
                   | (Node _, _)  => true
                   | _            => false
                   end
           |}.
    intros [??] [??] [E1 E2]. simpl in *.  subst. auto.
  Defined.
  Instance TreeF (A : Type) : Container (Ts A) Tp :=
    { dom := t_dom A }.
  Definition Tree A := LFix (TreeF A).

  Lemma dom_leaf_false A : Pos (F:=TreeF A) (Leaf A) -> False.
  Proof. intros []. simpl in *. discriminate. Qed.
  Definition dom_leaf A B (x : Pos (F:=TreeF A) (Leaf A)) : B :=
    False_rect _ (dom_leaf_false x).

  Definition a_leaf (A X : Type)
    : App (TreeF A) X := MkCont (Leaf A) (@dom_leaf A X).
  Arguments a_leaf & {A X}.
  Definition a_node A X (x : A) (l r : X) : App (TreeF A) X :=
    MkCont (Node x) (fun p => match val p with
                              | Lbranch => l
                              | Rbranch => r
                              end).
  Arguments a_node & {A X}.

  Definition a_out A X (x : App (TreeF A) X)
    : option (A * X * X)
    :=
    let (s, k) := x in
       match s return (Pos s -> X) -> _ with
       | Leaf _ => fun _ => None
       | Node x =>
           fun k=>
             Some (x,
                 k (MkElem Lbranch eq_refl),
                 k (MkElem Rbranch eq_refl))
       end k.
  (* end tree *)
  (* Definition p_app `{equiv A} : App (Prod Id Id) (list A) ~> list A. *)
  (*   refine {| *)
  (*       app := *)
  (*         fun x => Datatypes.app (from_id (fproj1 x)) (from_id (fproj2 x)) *)
  (*     |}. *)
  (*   intros [sx kx] [sy ky] [Es Ek]; simpl in *. *)
  (*   revert kx Ek. rewrite Es. clear Es sx. intros kx Ek. *)
  (*   unfold einl, einr. simpl. *)
  (*   assert (Rx : *)
  (*            (kx {| val := inl tt; InDom := eq_refl |}) = *)
  (*            (ky {| val := inl tt; InDom := eq_refl |})) by apply Ek. *)
  (*   assert (Ry : *)
  (*            (kx {| val := inr tt; InDom := eq_refl |}) = *)
  (*            (ky {| val := inr tt; InDom := eq_refl |})) by apply Ek. *)
  (*   simpl in *. rewrite Rx, Ry. reflexivity. *)
  (* Defined. *)

  (* Definition m_merge : App (TreeF nat) (list nat) ~> list nat. *)
  (*   unfold TreeF. *)
  (*   refine (fcase (tconst nil) _). *)

  (*   refine (fpair _ _). *)

  (*   About fproj1. *)
  (*   := *)
  (*   match a_out x with *)
  (*   | None => nil *)
  (*   | Some (h, l, r) => Datatypes.app l (h :: r) *)
  (*   end. *)

  Definition merge : Alg (TreeF nat) (list nat).
    refine {|
        app := fun (x : App (TreeF nat) (list nat)) =>
                 match a_out x with
                 | None => nil
                 | Some (h, l, r) => Datatypes.app l (h :: r)
                 end
      |}.
    intros [[|hx] kx] [[|hy] ky] [Hs Hk]; simpl in *; try discriminate; auto.
    inversion Hs. subst. clear Hs.
    set (R1 := Hk (MkElem Lbranch eq_refl) (MkElem Lbranch eq_refl) eq_refl).
    set (R2 := Hk (MkElem Rbranch eq_refl) (MkElem Rbranch eq_refl) eq_refl).
    simpl in *.
    rewrite R1,R2. reflexivity.
  Defined.

  Definition c_split : CoAlg (TreeF nat) (list nat).
    refine {|
        app := fun x =>
                 match x with
                 | nil => a_leaf
                 | cons h t =>
                     let l := List.filter (fun x => Nat.leb x h) t in
                     let r := List.filter (fun x => negb (Nat.leb x h)) t in
                     a_node h l r
                 end
      |}.
    intros x y ->. auto with ffix.
  Defined.

  Lemma length_filter A (p : A -> bool) (l : list A) n :
    Nat.leb (length l) n = true ->
    Nat.leb (length (List.filter p l)) n = true.
  Proof with (simpl in *; try discriminate; auto).
    revert n.
    induction l as [|h t Ih]...
    intros [|n]...
    destruct (p h)...
    intros H. specialize (Ih n H). clear H.
    generalize dependent (length (List.filter p t)). intros m. revert n.
    induction m as [|m Ih]; intros n; auto.
    destruct n as [|n]; simpl in *; try discriminate. apply Ih.
  Qed.
  (* Needs to be defined, otherwise qsort does not reduce!
   * UPDATE 12/09/2023 by DC: what's the nonsense above???
   *)
  Lemma split_fin : forall x, FinF c_split x.
  Proof.
    intros x. generalize (PeanoNat.Nat.leb_refl (List.length x)).
    generalize (length x) at 2. intros n. revert x.
    induction n as [|n Ih]; intros [|h t] H; simpl in *; try discriminate;
      constructor; intros e; try destruct (dom_leaf_false e).
    destruct e as [se ke].
    destruct se; simpl in *; apply Ih, length_filter, H.
  Qed.

  Definition tsplit : FCoAlg (TreeF nat) (list nat)
    := exist _ c_split split_fin.


  (* YAY! quicksort in Coq as a divide-and-conquer "finite" hylo :-) *)
  (* UPDATE 12/09/2023 by DC: this used to be mergesort, and at some
   * point I simply changed the implementation ...
   *)
  Definition qsort : list nat -> list nat := hylo merge tsplit.
End ExQsort.


Require Import Program.

Program Fixpoint qsort_proc (l : list nat) {measure (length l)} :=
  match l with
  | nil => nil
  | cons h t => qsort_proc (List.filter (fun x => Nat.leb x h) t) ++
                  h :: qsort_proc (List.filter (fun x => negb (Nat.leb x h)) t)
  end%list.
Next Obligation.
  simpl. clear qsort_proc. induction t; simpl; auto.
  elim (Nat.leb a h); simpl.
  - apply Arith_prebase.lt_n_S_stt, IHt.
  - apply PeanoNat.Nat.lt_lt_succ_r, IHt.
Qed.
Next Obligation.
  simpl. clear qsort_proc. induction t; simpl; auto.
  elim (Nat.leb a h); simpl.
  - apply PeanoNat.Nat.lt_lt_succ_r, IHt.
  - apply Arith_prebase.lt_n_S_stt, IHt.
Qed.

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extract Inlined Constant Nat.leb => "(<=)".
Set Extraction TypeExpand.
(* Set Extraction Conservative Types. *)
Extraction Inline projT1.
Extraction Inline projT2.
Extraction Inline comp.

Extraction Inline app.
Extraction Inline coalg.
Extraction Inline val.
Extraction Inline shape.
Extraction Inline cont.
Extraction Inline hylo.
Extraction Inline hylo_f.
Extraction Inline hylo_f_.

Extraction Inline merge.
Extraction Inline a_leaf.
Extraction Inline a_node.
Extraction Inline a_out.
Extraction Inline c_split.
Extraction Inline tsplit.
Set Extraction Flag 2047.
Recursive Extraction qsort.
