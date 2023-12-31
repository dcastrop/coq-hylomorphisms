Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import HYLO.Equivalence.
Require Import HYLO.Morphism.

(** The justification why the class below this comment defines a Container can be
  * found later, with the definitions: App, fmapA, etc.
  * - [S] is the type of "shapes" of this Container
  * - [P] is the type of "positions" in a shape
  * - [dom] determines whether a position is valid in a shape
  *
  * It is defined as a class to help extract cleaner code to OCaml.
  * An alternative definition, closer to the literature, would be to have
  * a record,
  * [ Record Container :=
      { shape : Type;
        position : Type;
        dom : shape -> position -> bool;
      }
    ]
  * use dependent types,
  * [ Record Container :=
      { shape : Type;
        position : shape -> Type;
      }
    ]
  * or even a straightforward "strict-positivisation" of an actual functor [F]:
  * [ Record Apply (F : Type -> Type) (X : Type) :=
      { witness : Type;
        shape : F witness;
        position : witness -> X;
      }
    ]
  * However, these alternatives would lead to lots of [Obj.magic] in the
  * generated OCaml code, and a priority of this experiment was extracting
  * "somewhat reasonable/clean" OCaml code.
  *)
Class Container `{Esh : equiv Sh} (P : Type) :=
  { dom : Sh * P ~> bool
  }.
Arguments Container Sh {Esh} P.

Record Pos `{Container Sh P} (s : Sh) :=
  MkElem {
      val : P;
      InDom : dom (s, val) = true
    }.
Arguments Pos & {Sh _ P F} s : rename.
Arguments MkElem & {Sh _ P F s} val InDom : rename.
Arguments val & {Sh _ P F s} : rename.
Arguments InDom & {Sh _ P F s} : rename.

Lemma elem_val_eq `{Container Sh P} (s : Sh) (e1 e2 : Pos s)
  : val e1 = val e2 -> e1 = e2.
Proof.
  destruct e1 as [v1 d1], e2 as [v d2]; simpl in *.
  intros; subst. rewrite (bool_irrelevance d1 d2). auto.
Qed.

Lemma elem_dom_irr `{Container Sh P} (s1 s2 : Sh) (Eq : s1 =e s2)
  : forall e1 : Pos s1, exists e3 : Pos s2, val e1 = val e3.
Proof.
  intros [v d1]. simpl.
  assert (d2 : dom (s2, v) =e true).
  { rewrite <- d1. apply app_eq. split; simpl; auto with ffix. }
  simpl in *.
  exists (MkElem v d2); auto.
Qed.

Record App `{F : Container Sh P} (X : Type) :=
  MkCont
    { shape : Sh;
      cont : Pos shape -> X
    }.
Arguments App {Sh _ P} F X.
Arguments cont {Sh _ P F X} a k.
Arguments MkCont {Sh _ P F X} shape cont.

Lemma cont_dom_irrelevant `{F : Container Sh Po} (X : Type) :
  forall (x : App F X) (e1 e2 : Pos (shape x)),
    val e1 = val e2 -> cont x e1 = cont x e2.
Proof.
  intros [s p]. simpl. intros [e1 d1] [e2 d2]. simpl. intros Eq. subst.
  rewrite (bool_irrelevance d1 d2).
  reflexivity.
Qed.

Inductive AppR `{F : Container Sh P} (X : Type) {e : equiv X}
           (x y : App F X) : Prop :=
  | AppR_ext
      (Es : shape x =e shape y)
      (Ek : forall e1 e2, val e1 = val e2 -> cont x e1 =e cont y e2).
#[export]
  Hint Constructors AppR : ffix.

#[export]
  Instance App_equiv `{F : Container Sh P} `{e : equiv X} : equiv (App F X).
Proof with eauto with ffix.
  apply (@MkEquiv _ (@AppR Sh _ P F X e)).
  - intros [shx kx]. constructor...
    simpl.  intros [x1 d1] [x2 d2] Eq. simpl in *. subst.
    rewrite (bool_irrelevance d1 d2).
    reflexivity.
  - intros x y [Sxy Exy]. split...
  - intros x y z [Sxy Exy] [Syz Eyz]; simpl; split.
    * rewrite Sxy...
    * intros e1 e2 V1.
      destruct (elem_dom_irr Sxy e1) as [e3 V2].
      apply (e_trans (Exy e1 e3 V2)), Eyz.
      rewrite <- V2. trivial.
Defined.

Lemma fold_eq A (x y : A) : x =e y -> x = y.
Proof. trivial. Qed.

Definition ComposeDom `(F : Container S1 P1) `(G : Container S2 P2) :
  @morph (App F S2 * (P1 * P2))
    (pair_eq (eq_B := def_eq (P1 * P2))) bool (def_eq bool).
  refine
    {| app :=
        fun (sp : App F S2 * (P1 * P2)) =>
          let (s , p12) := sp in
          let (p1 , p2) := p12 in
          match dom (shape s, p1) as b
                return dom (shape s, p1) = b -> bool
          with
          | true => fun H =>
                      let e := MkElem p1 H in
                      let kp := cont s e in
                      dom (kp, p2)
          | false => fun _ => false
          end eq_refl
    |}.
  intros [a [pa1 pa2]] [b [pb1 pb2]] [aRb E12]; simpl in *.
  inversion E12. rename H0 into E1. rename H1 into E2.
  destruct aRb as [Es Ek].
  assert (Dab : dom (shape a, pa1) =e dom (shape b, pb1)).
  { apply app_eq. split; trivial. }
  simpl in Dab. subst.
  generalize (@eq_refl _ (dom (shape a, pb1))).
  generalize (@eq_refl _ (dom (shape b, pb1))).
  revert Dab.
  generalize (dom (shape a, pb1)) at 1 3 4. intros []; simpl in *.
  + generalize (dom (shape b, pb1)) at 1 3 4. intros []; try discriminate.
    intros _ d1 d2. apply fold_eq, app_eq. split; simpl in *; trivial.
    apply Ek; trivial.
  + generalize (dom (shape b, pb1)) at 1 3 4. intros []; try discriminate.
    trivial.
Defined.
Arguments ComposeDom {S1 Esh P1} F {S2 Esh0 P2} G.

#[export]
  Instance CompCont `(F : Container S1 P1) `(G : Container S2 P2) :
  Container (App F S2) (P1 * P2) :=
  {
    dom := ComposeDom F G
  }.

Lemma cont_ext_eq `{F : Container Sh P} (s : Sh) `{equiv X}
  (k k' : Pos s -> X)
  : (forall x, k x =e k' x) -> AppR (MkCont s k) (MkCont s k').
Proof with simpl in *; auto with ffix.
  intros Heq. constructor...
  intros e1 e2 Hv. rewrite (elem_val_eq Hv)...
Qed.

Definition fmapA `{F : Container Sh P} `{equiv A} `{equiv B}
  (f : A -> B) (x : App F A) : App F B
  := MkCont (shape x) (fun e => f (cont x e)).

Lemma fmapA_eqF `{F : Container Sh P} `{equiv A} `{equiv B} (f : A ~> B)
  : forall (x y : App F A), x =e y -> fmapA (F:= F) f x =e fmapA f y.
Proof with eauto with ffix.
  intros [sx kx] [sy ky] [Es Ek]. split; auto. intros.  apply app_eq. auto.
Qed.

Notation fmapU f :=
  ({| app := fun x => MkCont (shape x) (fun e => f (cont x e));
     app_eq := fmapA_eqF f
   |}).

Lemma fmapU_eq `{F : Container Sh P} `{eA : equiv A} `{eB : equiv B} :
  forall f g : A ~> B, f =e g -> fmapU f =e fmapU g.
Proof.
  intros f g Hfg [sh p]. simpl.
  apply cont_ext_eq.
  intros. apply Hfg.
Qed.

Definition fmap `{F : Container Sh P} `{eA : equiv A} `{eB : equiv B} :
  (A ~> B) ~> App F A ~> App F B := MkMorph fmapU_eq.

Lemma fmap_id `{F : Container Sh P} `{equiv A} : fmap (F:=F) (id (A:=A)) =e id.
Proof. intros []; reflexivity. Qed.

Lemma fmap_comp `{F : Container Sh P} `{equiv A} `{equiv B} `{equiv C}
  (f : B ~> C) (g : A ~> B) : fmap (F:=F) (f \o g) =e fmap f \o fmap g.
Proof. intros []. reflexivity. Qed.
