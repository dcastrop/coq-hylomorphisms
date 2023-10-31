Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import HYLO.Equivalence.
Require Import HYLO.Morphism.
Require Import HYLO.Container.
Require Import HYLO.Algebra.
Require Import HYLO.Coalgebra.
Require Import HYLO.FCoalgebra.
Require Import HYLO.Hylo.

Require List.

(* Defining a tree *)

Unset Auto Template Polymorphism.

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
#[local]
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

Definition c_split : Coalg (TreeF nat) (list nat).
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
Lemma split_fin : forall x, RecF c_split x.
Proof.
  intros x. generalize (PeanoNat.Nat.leb_refl (List.length x)).
  generalize (length x) at 2. intros n. revert x.
  induction n as [|n Ih]; intros [|h t] H; simpl in *; try discriminate;
    constructor; intros e; try destruct (dom_leaf_false e).
  destruct e as [se ke].
  destruct se; simpl in *; apply Ih, length_filter, H.
Qed.

Definition tsplit : RCoalg (TreeF nat) (list nat)
    := exist _ c_split split_fin.


(* YAY! quicksort in Coq as a divide-and-conquer "finite" hylo :-) *)
(* UPDATE 12/09/2023 by DC: this used to be mergesort, and at some
 * point I simply changed the implementation ...
 *)
Definition qsort : Spec (cata merge \o rana tsplit).
  calculate.
  rewrite cata_ana_hylo.
  reflexivity.
Defined.


From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extract Inlined Constant Nat.leb => "(<=)".
Set Extraction TypeExpand.
(* Set Extraction Conservative Types. *)
Extraction Inline dom_leaf.
Extraction Inline projT1.
Extraction Inline projT2.
Extraction Inline comp.

Extraction Inline val.
Extraction Inline InDom.

Extraction Inline app.
Extraction Inline coalg.
Extraction Inline val.
Extraction Inline shape.
Extraction Inline cont.
Extraction Inline hylo.
Extraction Inline cata.
Extraction Inline ana.
Extraction Inline rana.
Extraction Inline hylo_f.
Extraction Inline hylo_f_.
Extraction Inline LFix_out.

Extraction Inline merge.
Extraction Inline a_leaf.
Extraction Inline a_node.
Extraction Inline a_out.
Extraction Inline c_split.
Extraction Inline tsplit.
Set Extraction Flag 2047.
Recursive Extraction qsort.
