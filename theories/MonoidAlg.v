Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Equivalence.
Require Import Hylo.Morphism.
Require Import Hylo.Container.
Require Import Hylo.Algebra.
Require Import Hylo.Coalgebra.
Require Import Hylo.FCoalgebra.
Require Import Hylo.Hylomorphisms.
Require Import Hylo.FiniteCont.

From Stdlib Require Import List.

(** Monoid algebras: algebras that fold a monoid over the children of a
  * finite container.
  *)

(** * Monoids *)

Record Monoid W `{eW : setoid W} :=
  MkMonoid
    { skip : W;
      par : W -> W -> W;
      par_proper : forall a1 a2 b1 b2, a1 =e a2 -> b1 =e b2 -> par a1 b1 =e par a2 b2;
      par_assoc : forall a b c, par a (par b c) =e par (par a b) c;
      par_skip_l : forall a, par skip a =e a;
      par_skip_r : forall a, par a skip =e a;
    }.
Arguments Monoid W {_}.

Record MonoidHom `{eW : setoid W} `{eV : setoid V}
  (M : Monoid W) (N : Monoid V) (h : W ~> V) : Prop :=
  { hom_skip : h (skip M) =e skip N;
    hom_par : forall a b, h (par M a b) =e par N (h a) (h b);
  }.

Section MConcat.
  Context `{eW : setoid W} (M : Monoid W).

  (** Fold a list with [par], adding no units: [mconcat [x] = x]. *)
  Fixpoint mconcat (l : list W) : W :=
    match l with
    | nil => skip M
    | x :: l' =>
        match l' with
        | nil => x
        | _ :: _ => par M x (mconcat l')
        end
    end.

  Lemma mconcat_proper (l1 l2 : list W)
    : Forall2 eqRel l1 l2 -> mconcat l1 =e mconcat l2.
  Proof.
    induction 1 as [|x1 x2 l1 l2 Ex El Ih]; simpl; [reflexivity|].
    destruct El; trivial.
    apply par_proper; trivial.
  Qed.

End MConcat.

Lemma mconcat_hom `{eW : setoid W} `{eV : setoid V} (M : Monoid W) (N : Monoid V)
  (h : W ~> V) (Hh : MonoidHom M N h) (l : list W)
  : h (mconcat M l) =e mconcat N (map h l).
Proof.
  induction l as [|x l Ih]; simpl; [apply hom_skip, Hh|].
  destruct l as [|y l]; [reflexivity|].
  rewrite (hom_par Hh). apply par_proper; [reflexivity|apply Ih].
Qed.

(** * Optional values *)

#[export] Instance option_eq `{eA : setoid A} : setoid (option A).
Proof.
  apply (@MkSetoid _ (fun x y =>
                        match x, y with
                        | None, None => True
                        | Some u, Some v => u =e v
                        | _, _ => False
                        end)).
  - intros []; auto with ffix.
  - intros [] []; auto with ffix.
  - intros [x|] [y|] [z|]; simpl; eauto with ffix; intros [].
Defined.
#[export] Instance option_no_def_eq A : NoDefEq (option A) := {}.

Section OMap.
  Context `{eA : setoid A} `{eB : setoid B}.

  Definition omap_ (f : A ~> B) (x : option A) : option B :=
    match x with
    | None => None
    | Some a => Some (f a)
    end.

  Lemma omap_morph (f : A ~> B) : forall x y, x =e y -> omap_ f x =e omap_ f y.
  Proof. intros [x|] [y|]; simpl; auto with ffix. Qed.

  Definition omap (f : A ~> B) : option A ~> option B := MkMorph (omap_morph f).
End OMap.

Definition opt_cons {A} (o : option A) (l : list A) : list A :=
  match o with
  | None => l
  | Some x => x :: l
  end.

Lemma opt_cons_proper `{setoid A} (o1 o2 : option A) (l1 l2 : list A)
  : o1 =e o2 -> Forall2 eqRel l1 l2 -> Forall2 eqRel (opt_cons o1 l1) (opt_cons o2 l2).
Proof. destruct o1, o2; simpl; try intros []; auto. Qed.

Lemma Forall2_eqRel_refl `{setoid A} (l : list A) : Forall2 eqRel l l.
Proof. induction l; constructor; auto with ffix. Qed.

Lemma map_opt_cons {A B} (f : A -> B) (o : option A) (l : list A)
  : map f (opt_cons o l) = opt_cons (option_map f o) (map f l).
Proof. destruct o; reflexivity. Qed.

(** * Monoid algebras *)

Section MAlg.
  Context `{Esh : setoid Sh} {P : Type} (F : FinCont Sh P) `{eW : setoid W} (M : Monoid W).

  Abbreviation FC := (fin_cont F).

  Lemma map_cont_rel (s1 s2 : Sh) (k1 : Pos FC s1 -> W) (k2 : Pos FC s2 -> W)
    (Ek : forall e1 e2, val e1 = val e2 -> k1 e1 =e k2 e2)
    : forall (l1 : list (Pos FC s1)) (l2 : list (Pos FC s2)),
      map val l1 = map val l2 -> Forall2 eqRel (map k1 l1) (map k2 l2).
  Proof.
    induction l1 as [|e1 l1 Ih]; intros [|e2 l2]; simpl; try discriminate; auto.
    intros E. injection E as Ev El. constructor; auto.
  Qed.

  (** A node folds its own value [leaf s], if any, and its children, in the
    * order of [elems]. *)
  Definition malg_ (leaf : Sh ~> option W) (x : App FC W) : W :=
    let (s, k) := x in mconcat M (opt_cons (leaf s) (map k (elems F s))).

  Lemma malg_morph (leaf : Sh ~> option W)
    : forall x y, x =e y -> malg_ leaf x =e malg_ leaf y.
  Proof.
    intros [sx kx] [sy ky] [Es Ek]; simpl in *.
    apply mconcat_proper, opt_cons_proper.
    - apply app_eq, Es.
    - apply map_cont_rel; trivial.
      rewrite !elems_val, (positions_proper F Es). reflexivity.
  Qed.

  Definition malg (leaf : Sh ~> option W) : Alg FC W := MkMorph (malg_morph leaf).
End MAlg.

(** * Fusion with monoid homomorphisms *)

Section Fusion.
  Context `{Esh : setoid Sh} {P : Type} (F : FinCont Sh P).
  Context `{eW : setoid W} `{eV : setoid V} (M : Monoid W) (N : Monoid V).
  Context (h : W ~> V) (Hh : MonoidHom M N h).

  Lemma malg_hom (leaf : Sh ~> option W)
    : h \o malg F M leaf =e malg F N (omap h \o leaf) \o fmap h.
  Proof.
    intros [s k]. simpl.
    rewrite (mconcat_hom Hh). apply mconcat_proper.
    rewrite map_opt_cons, map_map.
    destruct (leaf s); apply Forall2_eqRel_refl.
  Qed.

  (** Fusion: a monoid homomorphism after a monoid-algebra hylomorphism is
    * the hylomorphism of the mapped monoid algebra. Read right to left, it is
    * fission. *)
  Lemma malg_fusion `{eA : setoid A} (leaf : Sh ~> option W) (c : RCoalg (fin_cont F) A)
    : h \o hylo (malg F M leaf) c =e hylo (malg F N (omap h \o leaf)) c.
  Proof. apply hylo_fusion_l, malg_hom. Qed.
End Fusion.
