From mathcomp Require Import all_ssreflect.
From Paco Require Import paco paco2.
Require Import Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "x =l y" (at level 70, no associativity).
Reserved Notation "x =g y" (at level 70, no associativity).
Reserved Notation "x =a/g y" (at level 70, no associativity).
Reserved Notation "x '=1/g' y" (at level 70, no associativity).
Reserved Notation "x '=1/a' y" (at level 70, no associativity).
Reserved Notation "x '=1/a/g' y" (at level 70, no associativity).
Reserved Notation "x '=1/sval' y" (at level 70, no associativity).

(****************************************************************************)
(** Assumptions and Strict positivisation of functors                      **)
(****************************************************************************)

Structure equivalence A :=
  mkEquiv { eqRel : A -> A -> Prop;
            e_refl : forall x, eqRel x x;
            e_sym : forall x y, eqRel x y -> eqRel y x;
            e_trans : forall x y z, eqRel x y -> eqRel y z -> eqRel x z;
          }.

Hint Resolve e_refl : ffix.
Hint Resolve e_sym : ffix.
Hint Resolve e_trans : ffix.

Definition def_eq A : equivalence A :=
  {| eqRel := @eq A;
     e_refl := @erefl A;
     e_sym := @esym A;
     e_trans := @etrans A;
  |}.

Structure TyEq :=
  { Ty : Type;
    Eq : equivalence Ty
  }.
Coercion getTy (T : TyEq) := Ty T.

Coercion mkTy (A : Type) : TyEq :=
  {| Ty := A;
     Eq := def_eq A;
  |}.

Add Parametric Relation (A: TyEq) : A (eqRel (Eq A))
    reflexivity proved by (@e_refl A (Eq A))
    symmetry proved by (@e_sym A (Eq A))
    transitivity proved by (@e_trans A (Eq A))
      as ExtEq.

Reserved Notation "f =e g" (at level 70, no associativity).
(* Reserved Notation "f =1e g" (at level 70, no associativity). *)
Notation "f =e g" := (eqRel (Eq _) f g).
(* Notation "f =1e g" := (forall x, eqRel (Eq _) (f x) (g x)). *)

Definition extEq (A : TyEq) (B : Type) : equivalence (B -> A).
Proof.
  apply: (@mkEquiv _ (fun f g =>forall x, eqRel (Eq A) (f x) (g x))).
  - by move=>f x; apply: e_refl.
  - by move=>f g H x; apply: e_sym.
  - by move=>f g h Hf Hg x; apply: e_trans.
Defined.

Structure Functor :=
  { Shape : Type;
    Position : Type;
    (** Is position valid in shape? *)
    dom : Shape -> Position -> bool;
  }.

Definition Cont F (sh : Shape F) (X : TyEq)
  := {| Ty := sig (dom sh) -> X; Eq := extEq X _ |}.

Definition AppT F (X : Type) := {sh : Shape F & sig (dom sh) -> X}.

Lemma cont_irr F X (sh : Shape F) (f : sig (dom sh) -> X)
  : forall x p1 p2, f (exist _ x p1) = f (exist _ x p2).
Proof. move=> x/= p1 p2; by rewrite (bool_irrelevance p1 p2). Qed.

Definition AppR F (X : TyEq) (x y : AppT F X) : Prop
  := projT1 x = projT1 y /\
     (forall e d1 d2, projT2 x (exist _ e d1) =e projT2 y (exist _ e d2)).

Lemma AppR_inv_sh F X x y :
  @AppR F X x y -> projT1 x = projT1 y.
Proof. by case. Qed.

Lemma AppR_inv_k F X x y :
  @AppR F X x y ->
  forall e d1 d2, projT2 x (exist _ e d1) =e projT2 y (exist _ e d2).
Proof. by case. Qed.

Definition equivApp F (X : TyEq) : equivalence (AppT F X).
Proof.
  apply: (@mkEquiv _ (@AppR F X)).
  - move=> [shx kx]; constructor=>//=x d1 d2.
    rewrite (bool_irrelevance d1 d2); by apply: e_refl.
  - move=> x y [Sxy Exy]; split; first by apply/esym.
    by move=> e d1 d2; symmetry.
  - move=> x y z [Sxy Exy] [Syz Eyz]; split; first by rewrite Sxy.
    move=>e d1 d2; have d3: dom (projT1 y) e by move: d1; rewrite Sxy.
    rewrite (Exy e d1 d3) (Eyz e d3 d2); by reflexivity.
Defined.

Definition App F (X : TyEq)
  := {| Ty := AppT F X; Eq := equivApp F X |}.

Structure arr (A B : TyEq) :=
  { func :> Ty A -> Ty B;
    f_eq : forall x y, x =e y -> func x =e func y
  }.

Definition arrE (A B : TyEq) : equivalence (arr A B).
Proof.
  apply: (@mkEquiv _ (fun (f g : arr A B) => forall x, f x =e g x)).
  - by move=>x/=; auto with ffix.
  - by move=>x y/= H e; rewrite H; auto with ffix.
  - by move=>x y z/= H1 H2 e; rewrite H1.
Defined.

Definition arrow A B : TyEq :=
  {| Ty := arr A B;
     Eq := arrE A B;
  |}.

Definition fmapA_f F A B (f : arrow A B) (x : App F A) : App F B
  := existT _ (projT1 x) (f \o projT2 x).

Lemma fmapA_eqF F A B (f : arrow A B)
  : forall x y, x =e y -> fmapA_f (F:=F) f x =e fmapA_f f y.
Proof.
  move=> [sx kx] [sy ky] [/=Es Ek]; split=>//= e d1 d2.
  by apply/f_eq/Ek.
Qed.

Definition fmapA F A B (f : arrow A B) : arrow (App F A) (App F B)
  := {| func := _ ; f_eq := fmapA_eqF f |}.

Lemma comp_eq A B C (f : arrow B C) (g : arrow A B) :
  forall x y, x =e y -> (f \o g) x =e (f \o g) y.
Proof. by move=> x y H; apply/f_eq/f_eq. Qed.

Definition acomp A B C (f : arrow B C) (g : arrow A B) : arrow A C :=
  {| func := _; f_eq := comp_eq f g |}.

Notation "f \o g" := (acomp f g).

Lemma id_eq (A : TyEq) : forall (x y : A), x =e y -> id x =e id y.
Proof. by []. Qed.

Definition id A : arrow A A :=
  {| func := _; f_eq := @id_eq A |}.

Lemma fmap_id F A : fmapA F (id A) =e id _.
Proof.
  move=> [s k]/=; rewrite /fmapA_f/=; split=>//= e d1 d2.
  rewrite (bool_irrelevance d2 d1); by reflexivity.
Qed.

Lemma fmap_comp F A B C (f : arrow B C) (g : arrow A B)
  : fmapA F (f \o g) =e fmapA F f \o fmapA F g.
Proof.
  move=> [s k]/=; rewrite /fmapA_f/=; split=>//= e d1 d2.
  rewrite (bool_irrelevance d2 d1); by reflexivity.
Qed.

Add Parametric Morphism F (A B : TyEq) : (@fmapA F A B)
    with signature
    (eqRel (Eq (arrow A B)))
      ==> (eqRel (Eq (arrow (App F A) (App F B))))
      as fmapMorphism.
Proof.
  move=> f1 f2 Ef [s k]; split=>//= e d1 d2.
  by rewrite (bool_irrelevance d1 d2).
Qed.

Add Parametric Morphism (A B C : TyEq) : (@acomp A B C)
    with signature
    (eqRel (Eq (arrow B C)))
      ==> (eqRel (Eq (arrow A B)))
      ==> (eqRel (Eq (arrow A C)))
      as compMorphism.
Proof.
  move=> f1 f2 Ef g1 g2 Eg x=>//=.
  by apply/(e_trans (Ef (g1 x)))/f_eq/Eg.
Qed.

Definition Alg F A := arrow (App F A) A.
Definition CoAlg F A := arrow A (App F A).

Inductive LFixT F : Type :=
| LFix_in (sh : Shape F): (sig (dom sh) -> LFixT F) -> LFixT F.

Definition l_shape F (x : LFixT F) :=
  match x with
  | LFix_in sh _ => sh
  end.
Definition l_cont F (x : LFixT F) :=
  match x return sig (dom (l_shape x)) -> LFixT F with
  | LFix_in _ k => k
  end.

Fixpoint LFixR F (x y : LFixT F) : Prop :=
  l_shape x = l_shape y /\
  forall e d1 d2,
      LFixR (@l_cont F x (exist _ e d1)) (@l_cont F y (exist _ e d2)).

Lemma LFixR_inv_sh F (x y : LFixT F) : LFixR x y -> l_shape x = l_shape y.
Proof. by case: x=>[sx kx]; case: y=>[sy ky] []. Qed.

Lemma LFixR_inv_k F (x y : LFixT F)
  : LFixR x y ->
    forall e d1 d2,
      LFixR (@l_cont F x (exist _ e d1)) (@l_cont F y (exist _ e d2)).
Proof. by case: x=>[sx kx]; case: y=>[sy ky] []. Qed.

Lemma LFixR_refl F x : @LFixR F x x.
Proof.
  elim: x=>// shx k Ih; constructor=>//=x p1 p2.
  by rewrite (bool_irrelevance p1 p2); apply: Ih.
Qed.

Lemma LFixR_sym F x y : @LFixR F x y -> @LFixR F y x.
Proof.
  elim: x => sx kx Ih in y *; case: y => sy ky /=[/esym-Sxy E].
  split=>// e d1 d2; by apply/Ih/E.
Qed.

Lemma LFixR_trans F x y z : @LFixR F x y -> @LFixR F y z -> @LFixR F x z.
Proof.
  elim: x=> sx kx Ih in y z *; case: y=> sy ky/=; case: z=> sz kz/=.
  move=> [Sxy Exy] [Syz Eyz]; split; first by rewrite Sxy.
  move=> e d1 d2; apply: Ih; first by apply: Exy; rewrite Syz.
  by apply/Eyz.
Qed.

Definition LFix_Eq F :=
  {| eqRel := @LFixR F;
     e_refl := @LFixR_refl F;
     e_sym := @LFixR_sym F;
     e_trans := @LFixR_trans F;
  |}.

Definition LFix F :=
  {| Ty := LFixT F; Eq := @LFix_Eq F; |}.

Definition l_in_f F (x : App F (LFix F)) : LFix F :=
  LFix_in (projT2 x).

Lemma l_in_eq F x y : x =e y -> @l_in_f F x =e @l_in_f F y.
Proof. by case: x=> sx kx; case: y=> sy ky/= [/=Es Ek]; split. Qed.

Definition l_out_f F (x : LFix F) : App F (LFix F) :=
  match x with
  | LFix_in sh k => existT _ sh k
  end.

Lemma l_out_eq F x y : x =e y -> @l_out_f F x  =e @l_out_f F y.
Proof. by case: x=> sx kx; case: y=> sy ky/= [/=Es Ek]; split. Qed.

Definition l_in F : Alg F (LFix F) :=
  {| func := _; f_eq := @l_in_eq F |}.
Definition l_out F : CoAlg F (LFix F) :=
  {| func := _; f_eq := @l_out_eq F |}.

Lemma l_in_out F : l_in F \o l_out F =e id _.
Proof.
  move=>[s k]/=; split=>//= e d1 d2; rewrite (bool_irrelevance d1 d2).
  by apply: LFixR_refl.
Qed.

Lemma l_out_in F : l_out F \o l_in F =e id _.
Proof.
  move=>[s k]/=; split=>//= e d1 d2; rewrite (bool_irrelevance d1 d2).
  by apply: LFixR_refl.
Qed.

Definition cata_f F A (g : Alg F A) : Ty (LFix F) -> Ty A
  := fix f x :=
       match x with
       | LFix_in s k => g (existT _ s (comp f k))
       end.

Lemma cata_arr F A (g : Alg F A) :
  forall x y, x =e y -> cata_f g x =e cata_f g y.
Proof.
  move=> x y /=; elim: x => sx kx Ih/= in y *; case: y=> sy ky/= [Es Ek].
  apply/(f_eq g); split=>//= e d1 d2; by apply/Ih.
Qed.

Definition cata F A (g : Alg F A) : arrow (LFix F) A
  := {| func := _; f_eq := cata_arr g |}.

Lemma cata_univ_r F A (g : Alg F A) (f : arrow (LFix F) A)
  : f =e g \o fmapA F f \o @l_out F -> f =e cata g.
Proof.
  move=> H.
  elim=> sx kx /= Ih.
  rewrite (H _)/=; apply/f_eq; rewrite /fmapA_f/=.
  split=>//= e d1 d2.
  rewrite Ih (cont_irr (X:=LFix F) kx).
  by auto with ffix.
Qed.

Lemma cata_univ_l F A (g : Alg F A) (f : arrow (LFix F) A)
  : f =e cata g -> f =e g \o fmapA F f \o @l_out F.
Proof.
  move=> H.
  elim=> sx kx /= Ih.
  rewrite (H _)/=; apply/(f_eq g); rewrite /fmapA_f/=.
  split=>//= e d1 d2.
  rewrite Ih (cont_irr (X:=LFix F) kx).
  rewrite -[cata_f g _]/(cata g _) -(H _) Ih.
  by auto with ffix.
Qed.

Lemma cata_univ F A (g : Alg F A) (f : arrow (LFix F) A)
  : f =e cata g <-> f =e g \o fmapA F f \o @l_out F.
Proof. by split;[apply/cata_univ_l|apply/cata_univ_r]. Qed.

(* Finite anamorphisms *)
Inductive FinF F A (h : CoAlg F A) : A -> Prop :=
| FinF_fold x : (forall e, FinF h (projT2 (h x) e)) -> FinF h x.

Lemma FinF_inv F A (h : CoAlg F A) x
  : FinF h x -> forall e, FinF h (projT2 (h x) e).
Proof. by case. Defined.

(* Finite coalgebras *)
Structure FCoAlg F A :=
  { coalg :> CoAlg F A;
    finite : forall x, FinF coalg x
  }.

Definition ana_f_ F A (h : CoAlg F A) : forall (x : A), FinF h x -> LFix F
  := fix f x H :=
       let hx := h x in
       LFix_in (fun e => f (projT2 hx e) (FinF_inv H e)).

Lemma ana_f_irr F A (h : CoAlg F A)
  : forall (x : A) (F1 F2 : FinF h x), ana_f_ F1 =e ana_f_ F2.
Proof.
  move=>/=; fix Ih 2; move=> x [{}x Fx] F2; move: F2 Fx=> [{}x Fy] Fx/=.
  split=>// e d1 d2; rewrite (bool_irrelevance d2 d1) => {d2}.
  by apply: Ih.
Qed.

Definition ana_f F A (h : FCoAlg F A) : A -> LFix F
  := fun x => ana_f_ (finite h x).

Lemma ana_arr F A (h : FCoAlg F A) :
  forall x y, x =e y -> ana_f h x =e ana_f h y.
Proof.
  rewrite /ana_f; move=> x y; move: x y (finite h x) (finite h y).
  fix Ih 3; move=> x y [x' Fx] [y' Fy]/=; split.
  - by case: (f_eq (coalg h) H).
  - move=> e d1 d2 /=; apply: Ih.
    by move: (f_eq (coalg h) H)=> [E1 /(_ e d1 d2)].
Qed.

Definition ana F A (h : FCoAlg F A) : arrow A (LFix F)
  := {| func := ana_f h; f_eq := ana_arr h |}.

Lemma ana_univ_r F A (h : FCoAlg F A) (f : arrow A (LFix F))
  : f =e @l_in F \o fmapA F f \o coalg h -> f =e ana h.
Proof.
  move=> H; rewrite /ana/ana_f/==>x; move: x (finite h x).
  fix Ih 2; move=> x [{}x Fx].
  rewrite -[LFixR (f x) _]/(eqRel (Eq _) (f x) _) (H _)/=; split=>// e d1 d2.
  rewrite (bool_irrelevance d2 d1); by apply: Ih.
Qed.

Lemma ana_univ_l F A (h : FCoAlg F A) (f : arrow A (LFix F))
  : f =e ana h -> f =e @l_in F \o fmapA F f \o coalg h.
Proof.
  move=> H x; move: x (finite h x).
  fix Ih 2; move=> x [{}x Fx].
  rewrite (H _) /=/ana_f; move: (finite h x)=>Fx'; move: Fx' Fx.
  move=>[{}x Fx'] Fx/=; split=>// e d1 d2.
  rewrite (bool_irrelevance d2 d1).
  rewrite -[LFixR _ _]/(eqRel (Eq _) _ _).
  move: (H (projT2 (coalg h x) (exist _ e d1))); rewrite /ana/ana_f/=.
  rewrite -![LFixR _ _]/(eqRel (Eq _) _ _).
  rewrite ana_f_irr =><-/=; by apply: LFixR_refl.
Qed.

Lemma ana_univ F A (h : FCoAlg F A) (f : arrow A (LFix F))
  : f =e ana h <-> f =e @l_in F \o fmapA F f \o coalg h.
Proof. by split;[apply/ana_univ_l|apply/ana_univ_r]. Qed.

(** Hylomorphisms **)

Definition hylo_f_ F A B (g : Alg F B) (h : CoAlg F A)
  : forall (x : A), FinF h x -> B
  := fix f x H :=
       let hx := h x in
       g (existT (fun sh=> sig (dom sh) -> B)
                 (projT1 hx)
                 (fun e => f (projT2 hx e) (FinF_inv H e))).

Lemma hylo_f_irr F A B (g : Alg F B) (h : CoAlg F A)
  : forall (x : A) (F1 F2 : FinF h x), hylo_f_ g F1 =e hylo_f_ g F2.
Proof.
  move=>/=; fix Ih 2; move=> x [{}x Fx] F2; move: F2 Fx=> [{}x Fy] Fx/=.
  apply/f_eq=>/=; split=>//= e d1 d2; rewrite (bool_irrelevance d2 d1)=>{d2}.
  by apply: Ih.
Qed.

Definition hylo_f F A B (g : Alg F B) (h : FCoAlg F A)
  := fun x => hylo_f_ g (finite h x).

Lemma hylo_arr F A B (g : Alg F B) (h : FCoAlg F A)
  : forall x y, x =e y -> hylo_f g h x =e hylo_f g h y.
Proof.
  rewrite /hylo_f; move=> x y; move: x y (finite h x) (finite h y).
  fix Ih 3; move=> x y [x' Fx] [y' Fy]/= H; apply/f_eq=>/=.
  case: (f_eq (coalg h) H)=>/= Es Ek; split=>//= e d1 d2.
  by apply/Ih/Ek.
Qed.

Definition hylo F A B (g : Alg F B) (h : FCoAlg F A) : arrow A B
  := {| func := _ ; f_eq := hylo_arr g h |}.

Lemma hylo_univ_r F A B (g : Alg F B) (h : FCoAlg F A) (f : arrow A B)
  : f =e g \o fmapA F f \o coalg h -> f =e hylo g h.
Proof.
  move=> H; rewrite /hylo/hylo_f/==>x; move: x (finite h x).
  fix Ih 2; move=> x Fx; rewrite (H _)/=/fmapA_f/=; case: Fx=> {}x Fx/=.
  apply/f_eq => /=; split=>//= e d1 d2.
  by rewrite (bool_irrelevance d2 d1); apply/Ih.
Qed.

Lemma hylo_univ_l F A B (g : Alg F B) (h : FCoAlg F A) (f : arrow A B)
  : f =e hylo g h -> f =e g \o fmapA F f \o coalg h.
Proof.
  move=> H x; move: x (finite h x).
  fix Ih 2; move=> x [{}x Fx].
  rewrite (H _) /=/hylo_f; move: (finite h x)=>Fx'; move: Fx' Fx.
  move=>[{}x Fx'] Fx/=; apply/f_eq; split=>//= e d1 d2.
  rewrite (bool_irrelevance d2 d1) (H _) /=/hylo_f/= hylo_f_irr.
  by eauto with ffix.
Qed.

Lemma hylo_univ F A B (g : Alg F B) (h : FCoAlg F A) (f : arrow A B)
  : f =e hylo g h <-> f =e g \o fmapA F f \o coalg h.
Proof. by split;[apply/hylo_univ_l|apply/hylo_univ_r]. Qed.

Corollary hylo_unr F A B (g : Alg F B) (h : FCoAlg F A)
  : hylo g h =e g \o fmapA F (hylo g h) \o coalg h.
Proof. by rewrite -hylo_univ; reflexivity. Qed.

Lemma fin_out F : forall x, FinF (@l_out F) x.
Proof. by elim=>s k Ih; constructor; apply: Ih. Qed.

Definition f_out F : FCoAlg F (LFix F) :=
  {| coalg := @l_out F; finite := @fin_out F|}.

Lemma hylo_cata F B (g : Alg F B)
  : cata g =e hylo g (f_out F).
Proof. rewrite hylo_univ; apply/cata_univ; reflexivity. Qed.

Lemma hylo_ana F A (h : FCoAlg F A)
  : ana h =e hylo (l_in F) h.
Proof. by rewrite hylo_univ; apply/ana_univ; reflexivity. Qed.

Lemma compA A B C D (f : arrow C D) (g : arrow B C) (h : arrow A B)
  : f \o (g \o h) =e (f \o g) \o h.
Proof. move=>x; by eauto with ffix. Qed.

Lemma idKl A B (f : arrow A B)
  : f \o id A =e f.
Proof. move=> x; by eauto with ffix. Qed.

Lemma idKr A B (f : arrow A B)
  : id B \o f  =e f.
Proof. move=> x; by eauto with ffix. Qed.

Lemma compKl A B C (f : arrow B C) (g1 g2 : arrow A B)
  : g1 =e g2 -> f \o g1 =e f \o g2.
Proof. by move=>->; eauto with ffix. Qed.

Lemma compKr A B C (f1 f2: arrow B C) (g : arrow A B)
  : f1 =e f2 -> f1 \o g =e f2 \o g.
Proof. by move=>->; eauto with ffix. Qed.

Lemma hylo_fusion_l F A B C
      (h1 : FCoAlg F A) (g1 : Alg F B) (g2 : Alg F C) (f2 : arrow B C)
      (E2 : f2 \o g1 =e g2 \o fmapA F f2)
  : f2 \o hylo g1 h1 =e hylo g2 h1.
Proof.
  rewrite hylo_univ fmap_comp.
  rewrite compA -E2 -compA -compA.
  apply/compKl.
  rewrite compA -hylo_univ.
  reflexivity.
Qed.

Lemma hylo_fusion_r F A B C
      (h1 : FCoAlg F B) (g1 : Alg F C) (h2 : FCoAlg F A)
      (f1 : arrow A B) (E1 : h1 \o f1 =e fmapA F f1 \o h2)
  : hylo g1 h1 \o f1 =e hylo g1 h2.
Proof.
  rewrite hylo_univ fmap_comp.
  rewrite -!compA -E1 !compA.
  apply/compKr.
  rewrite -hylo_univ.
  reflexivity.
Qed.

Lemma deforest F A B C
      (h1 : FCoAlg F A) (g1 : Alg F B) (h2 : FCoAlg F B) (g2 : Alg F C)
      (INV: h2 \o g1 =e id _)
  : hylo g2 h2 \o hylo g1 h1 =e hylo g2 h1.
Proof.
  apply/hylo_fusion_l.
  rewrite [in H in H =e _]hylo_unr.
  rewrite -compA INV idKl.
  reflexivity.
  Restart.
  apply/hylo_fusion_r.
  rewrite [in H in H =e _]hylo_unr.
  rewrite compA compA INV idKr.
  reflexivity.
Qed.

Corollary cata_ana_hylo F A B (g : Alg F B) (h : FCoAlg F A)
  : cata g \o ana h =e hylo g h.
Proof. by rewrite hylo_cata hylo_ana; apply/deforest/l_out_in. Qed.

Section ExQsort.

  (* Defining a tree *)
  Inductive Ts A :=
  | Leaf | Node (ELEM : A).
  Inductive Tp := | Lbranch | Rbranch.
  Definition t_dom A (s : Ts A) : Tp -> bool :=
    match s with
    | Node _ => fun=>true
    | _ => fun=> false
    end.
  Definition Tree A :=
    {| Shape := Ts A;
       Position := Tp;
       dom := @t_dom A;
    |}.
  Lemma dom_leaf_false A : {y | t_dom (Leaf A) y} -> False.
  Proof. by move=>[]. Qed.
  Definition dom_leaf A B (x : {y | t_dom (Leaf A) y}) : B :=
    False_rect _ (dom_leaf_false x).

  Definition a_leaf A X : App (Tree A) X := existT _ (Leaf A) (@dom_leaf A _).
  Definition a_node A X (x : A) (l r : X) : App (Tree A) X :=
    existT _ (Node x) (fun p => match proj1_sig p with
                                | Lbranch => l
                                | Rbranch => r
                                end).

  Definition a_out A X (x : App (Tree A) X)
    : option (A * X * X)
    := match x with
       | existT s k =>
         match s return (sig (t_dom s) -> X) -> _ with
         | Leaf => fun=> None
         | Node x =>
           fun k=>
             Some (x,
                   k (exist _ Lbranch is_true_true),
                   k (exist _ Rbranch is_true_true))
         end k
       end.
  (* end tree *)

  Definition m_merge (x : App (Tree nat) (seq nat)) : Ty (seq nat) :=
    match a_out x with
    | None => [::]
    | Some (h, l, r) => l ++ h :: r
    end.
  Lemma m_merge_arr : forall x y, x =e y -> m_merge x =e m_merge y.
  Proof.
    move=>[[|hx]/= kx]/= [[|hy]//= ky] [//= [<-]] H.
    by rewrite /m_merge/= !H.
  Qed.
  Definition merge : Alg (Tree nat) (seq nat)
    := {| func := m_merge; f_eq := m_merge_arr |}.

  Definition m_split (x : Ty (seq nat)) : App (Tree nat) (seq nat) :=
    match x with
    | [::] => a_leaf _ _
    | h :: t => a_node h [seq x <- t | x <= h] [seq x <- t | x > h]
    end.
  Lemma m_split_arr : forall x y, x =e y -> m_split x =e m_split y.
  Proof. by move=> x y ->; eauto with ffix. Qed.
  Definition c_split : CoAlg (Tree nat) (seq nat)
    := {| func := m_split; f_eq := m_split_arr |}.

  (* Needs to be defined, otherwise msort does not reduce! *)
  Lemma split_fin : forall x, FinF c_split x.
  Proof.
    move=>x; move: {-1}(size x) (leqnn (size x))=> n.
    elim: n => [|n Ih] in x *; case: x=> [|h t]/=; eauto=>E; constructor=>/=.
    - by case.
    - by [].
    - move=> [e /=_]; apply/Ih.
      by case: e; rewrite size_filter (leq_trans (count_size _ _)).
  Defined.

  Definition tsplit := {| coalg := c_split; finite := split_fin |}.
  Definition msort : seq nat -> seq nat := func (hylo merge tsplit).
End ExQsort.

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Set Extraction TypeExpand.
Set Extraction Flag 2047.
Extract Inductive sigT => "(*)"  [ "(,)" ].
Extraction Inline Ty.
Extraction Inline Eq.
Extraction Inline func.
Extraction Inline coalg.
Extraction Inline getTy.
Extraction Inline hylo.
Extraction Inline hylo_f.
Extraction Inline hylo_f_.
Extraction Inline projT1.
Extraction Inline projT2.

Extraction Inline merge.
Extraction Inline a_leaf.
Extraction Inline a_node.
Extraction Inline m_merge.
Extraction Inline m_split.
Extraction Inline a_out.
Extraction Inline c_split.
Extraction Inline tsplit.
Recursive Extraction msort.
