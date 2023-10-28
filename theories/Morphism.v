Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import HYLO.Equivalence.

Reserved Notation "x ~> y" (at level 95, right associativity, y at level 200).

Section Defn.
  Context `{eA : equiv A} `{eB : equiv B}.

  Structure morph :=
    MkMorph
      { app :> A -> B;
        app_eq : forall x y, x =e y -> app x =e app y
      }.
  Hint Resolve app_eq : ffix.

  #[export] Instance eq_morph : equiv morph.
  Proof with eauto with ffix.
    apply (@MkEquiv _ (fun f g =>forall x, app f x =e app g x))...
  Defined.
End Defn.
Arguments morph A {eA} B {eB}.
Notation "x ~> y" := (morph x y).

Lemma f_equal `{equiv A} `{equiv B} (f g : A ~> B)
  : forall x, f =e g -> f x =e g x.
Proof. intros x E. apply E. Qed.

Add Parametric Morphism `{eA : equiv A} `{eB : equiv B}
  : (@app A eA B eB)
    with signature
    (eqRel (A:=A~>B))
      ==> (eqRel (A:=A))
      ==> (eqRel (A:=B))
      as appMorphism.
Proof.
  intros ?? Efg x y Exy.
  rewrite (Efg x).
  apply app_eq, Exy.
Qed.

Section Id.
  Context `{eA : equiv A}.

  Notation id_ := (fun x => x).

  Lemma id_eq : forall x y : A, x =e y -> id_ x =e id_ y.
  Proof. auto. Qed.

  Definition id : A ~> A := {| app := _; app_eq := id_eq |}.
End Id.

Section Const.
  Context `{eA : equiv A} `{eB : equiv B}.
  Notation const_ := (fun (k : B) (_ : A) => k).

  Lemma const_eq1 (k : B)
    : forall x y : A, x =e y -> (const_ k) x =e (const_ k) y.
  Proof. auto with ffix. Qed.
  Definition const1 (k : B) : A ~> B
    := {| app := _; app_eq := const_eq1 k |}.


  Lemma const_eq : forall x y : B, x =e y -> const1 x =e const1 y.
  Proof. intros ????. trivial. Qed.

  Definition const : B ~> A ~> B := {| app := _; app_eq := const_eq |}.
End Const.


Section Exp.
  Context `{equiv A} `{equiv B} `{equiv C}.

  Notation eapp_ := (fun x : (_ ~> _) * _ => let (f, v) := x in f v).

  Lemma eapp_eq : forall x y : (A ~> B) * A, x =e y -> eapp_ x =e eapp_ y.
  Proof.
    intros [][][E1 E2]; simpl in *.
    rewrite (app_eq m E2). apply E1.
  Qed.

  Definition eapp := MkMorph eapp_eq.

  Notation papp_ f := (fun x y => f y x).
  Lemma papp_eq (f : A ~> B ~> C) (v : B)
    : forall x y : A, x =e y -> papp_ f v x =e papp_ f v y.
  Proof. intros ?? E. simpl. apply (f_equal v), app_eq,E. Qed.
  Definition papp f v := MkMorph (papp_eq f v).
End Exp.

Reserved Notation "f \o g" (at level 50, format "f  \o '/ '  g").
Section Comp.
  Context `{equiv A} `{equiv B} `{equiv C}.
  Notation comp_ := (fun f g => (fun x => f (g x))).

  Lemma comp_eq2 (g : B ~> C) (f : A ~> B)
    : forall x y, x =e y -> (comp_ g f) x =e (comp_ g f) y.
  Proof. intros. apply app_eq,app_eq. trivial. Qed.
  Notation comp2 := (fun g f => MkMorph (comp_eq2 g f)).

  Lemma comp_eq1 (g : B ~> C)
    : forall x y : A ~> B, x =e y -> (comp2 g) x =e (comp2 g) y.
  Proof. intros ?? E ?. simpl. apply app_eq, E. Qed.
  Notation comp1 := (fun g => MkMorph (comp_eq1 g)).

  Lemma comp_eq : forall x y : B ~> C, x =e y -> comp1 x =e comp1 y.
  Proof. intros ?? E ??. apply E. Qed.
  Definition comp : (B ~> C) ~> (A ~> B) ~> A ~> C := MkMorph comp_eq.
End Comp.
Notation "f \o g" := (comp f g).

Lemma compA `{equiv A} `{equiv B} `{equiv C} `{equiv D}
  (f : C ~> D) (g : B ~> C) (h : A ~> B) : f \o (g \o h) =e (f \o g) \o h.
Proof. intros x. simpl. reflexivity. Qed.
Lemma idKl `{equiv A} `{equiv B} (f : A ~> B) : id \o f =e f.
Proof. intros x. simpl. reflexivity. Qed.
Lemma idKr `{equiv A} `{equiv B} (f : A ~> B) : f \o id =e f.
Proof. intros x. simpl. reflexivity. Qed.

Section Pairs.
  Context `{eA : equiv A} `{eB : equiv B} `{eC : equiv C}.
  Notation fst_ := (fun x : _ * _ => let (y, _) := x in y).
  Notation snd_ := (fun x : _ * _ => let (_, y) := x in y).
  Lemma fst_eq :
    forall x y : A * B, x =e y -> fst_ x =e fst_ y.
  Proof. intros [][][]; trivial. Qed.
  Lemma snd_eq :
    forall x y : A * B, x =e y -> snd_ x =e snd_ y.
  Proof. intros [][][]; trivial. Qed.
  Definition fst : A * B ~> A := MkMorph fst_eq.
  Definition snd : A * B ~> B := MkMorph snd_eq.


  Notation pair_ f g := (fun x => (f x, g x)).

  Lemma pair_feq2 (f : A ~> B) (g : A ~> C) :
    forall x y : A, x =e y -> (pair_ f g) x =e (pair_ f g) y.
  Proof. intros; split; apply app_eq; trivial. Qed.

  Notation pair2 := (fun f g => MkMorph (pair_feq2 f g)).

  Lemma pair_feq1 (f : A ~> B)
    : forall x y : A ~> C, x =e y -> (pair2 f) x =e (pair2 f) y.
  Proof. intros ?? E ?. split; [reflexivity|apply E]. Qed.
  Notation pair1 := (fun f => MkMorph (pair_feq1 f)).

  Lemma pair_feq
    : forall x y : A ~> B, x =e y -> pair1 x =e pair1 y.
  Proof. intros ?? E ?. split; [apply E|reflexivity]. Qed.
  Definition pair := MkMorph pair_feq.
End Pairs.

Lemma fst_pair `{equiv A} `{equiv B} `{equiv C} (f : A ~> B) (g : A ~> C) :
  fst \o pair f g =e f.
Proof. intros x. simpl. reflexivity. Qed.
Lemma snd_pair `{equiv A} `{equiv B} `{equiv C} (f : A ~> B) (g : A ~> C) :
  snd \o pair f g =e g.
Proof. intros x. simpl. reflexivity. Qed.

Lemma pair_fusion `{equiv A} `{equiv B1} `{equiv B2} `{equiv C1} `{equiv C2}
  (h : A ~> B1) (i : A ~> B2) (f : B1 ~> C1) (g : B2 ~> C2)
  : pair (f \o fst) (g \o snd) \o pair h i =e pair (f \o h) (g \o i).
Proof. intros x. split; reflexivity. Qed.

Section Sums.
  Context `{equiv A} `{equiv B} `{equiv C}.
  Lemma inj1_eq : forall x y : A, x =e y -> inl x =e inl y.
  Proof. intros. simpl. trivial. Qed.
  Lemma inj2_eq : forall x y : A, x =e y -> inr x =e inr y.
  Proof. intros. simpl. trivial. Qed.
  Definition inj1 : A ~> A + C := MkMorph inj1_eq.
  Definition inj2 : A ~> C + A := MkMorph inj2_eq.

  Notation fcase_ f g
    := (fun x => match x with | inl y => f y | inr y => g y end).

  Lemma fcase_eq2 (f : A ~> C) (g : B ~> C) :
    forall x y : A + B, x =e y -> (fcase_ f g) x =e (fcase_ f g) y.
  Proof. intros [][]; simpl; try intros[]; apply app_eq; trivial. Qed.
  Notation fcase2 := (fun f g => MkMorph (fcase_eq2 f g)).

  Lemma fcase_eq1 (f : A ~> C) :
    forall x y : B ~> C, x =e y -> (fcase2 f) x =e (fcase2 f) y.
  Proof. intros ?? E []; simpl; try reflexivity; try apply E. Qed.
  Notation fcase1 := (fun f => MkMorph (fcase_eq1 f)).

  Lemma fcase_eq : forall x y : A ~> C, x =e y -> fcase1 x =e fcase1 y.
  Proof. intros ?? E [][]; simpl; try reflexivity; try apply E. Qed.
  Definition fcase := MkMorph fcase_eq.
End Sums.

Lemma inj1_case `{equiv A} `{equiv B} `{equiv C} (f : A ~> C) (g : B ~> C) :
  fcase f g \o inj1 =e f.
Proof. intros x. simpl. reflexivity. Qed.
Lemma inj2_case `{equiv A} `{equiv B} `{equiv C} (f : A ~> C) (g : B ~> C) :
  fcase f g \o inj2 =e g.
Proof. intros x. simpl. reflexivity. Qed.

Lemma eapp_pair_const `{equiv A} `{equiv B} `{equiv C}
  (f : B ~> C) (g : A ~> B) : eapp \o pair (const f) g =e f \o g.
Proof. intros x. simpl. reflexivity. Qed.

Lemma eapp_pair_id `{equiv A} `{equiv B} `{equiv C} (f : A ~> B ~> C) :
  eapp \o pair (const f) id =e f.
Proof. intros x. simpl. reflexivity. Qed.

Definition uncurry `{equiv A} `{equiv B} `{equiv C} (f : A ~> B ~> C)
    : A * B ~> C := eapp \o pair (f \o fst) snd.

Definition curry `{equiv A} `{equiv B} `{equiv C} (f : A * B ~> C)
  : A ~> B ~> C := comp f \o papp pair id \o const.


Section SpecDef.
  Context `{eA : equiv A} `{eB : equiv B}.
  Record Spec (f : A ~> B) :=
    MkSpec
      { target :> A ~> B;
        tgt_eq : f =e target;
      }.
End SpecDef.

Ltac calculate := eapply MkSpec.
