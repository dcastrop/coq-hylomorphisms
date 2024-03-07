Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import HYLO.Equivalence.
Require Import HYLO.Morphism.
Require Import HYLO.Container.
Require Import HYLO.Algebra.
Require Import HYLO.Coalgebra.
Require Import HYLO.FCoalgebra.
Require Import HYLO.Hylo.
Require Import HYLO.Extraction.

Require Import Util.Utils.

Require Import Examples.BTree.
Require Import Examples.CList.

Require Import List.
Require Import Coq.Numbers.Cyclic.Int63.Sint63.


(* Memoisation tables for a container C, indexed by 'A' *)
(** The container below is equivalent to:
 * [ CoInductive MemoTable `(C : Cont Sc Pc) A
   := Cons { head : A; tail : App C (MemoTable C A) }.
   ]
 *)
Section MemoTable.
  Context `(G : Cont Sg Pg) `{setoid A}.

  Definition MemoShape : Type := A * Sg.
  Definition MemoPos := Pg.
  Instance Memo : Cont MemoShape MemoPos
    := { valid := valid \o pair (snd \o fst) snd }.

  Definition Table := GFix Memo.

  Definition ConsT (x : A * App G Table)
    : App Memo Table :=
    match x with
    | (a, MkCont sx kx) =>
        {| shape := (a, sx);
          cont := fun e : Container.Pos (a, sx) =>
                    match e with
                    | MkElem e V => kx (MkElem e V)
                    end
        |}
    end.
  Lemma ConsT_morph : forall x y, x =e y -> ConsT x =e ConsT y.
  Proof.
    intros [ax [sx kx]] [ay [sy ky]] [Ea [St Kt]]. simpl in *.
    constructor; simpl; auto with ffix.
    intros [v1 V1] [v2 V2] Ev; simpl in *. subst.
    apply Kt. trivial.
  Qed.
  Definition Cons : A * App G Table ~> App Memo Table
    := Eval unfold ConsT in MkMorph ConsT_morph.

  Definition headT_ (t : Table) : A := fst (shape (g_out t)).
  Definition tailT_ (t : Table) : App G Table :=
    match g_out t with
    | {| shape := (a, st); cont := kt |} =>
        {| shape := st; cont := fun e =>
                                  match e with
                                  | MkElem v V => kt (MkElem v V)
                                  end
        |}
    end.
  Lemma headT_morph : forall x y, x =e y -> headT_ x =e headT_ y.
  Proof.
    intros x y Exy.
    unfold headT_. apply GFixR_unfold in Exy. destruct Exy as [Sxy Kxy].
    replace (GFix_out x) with (g_out x) in * by reflexivity.
    replace (GFix_out y) with (g_out y) in * by reflexivity.
    destruct (g_out x) as [sx kx], (g_out y) as [sy ky]. simpl in *.
    destruct sx as [ax tx], sy as [ay ty], Sxy as [Sxy _]; simpl in *; trivial.
  Qed.
  Definition headT := Eval unfold headT_ in MkMorph headT_morph.

  Lemma tailT_morph : forall x y, x =e y -> tailT_ x =e tailT_ y.
  Proof.
    intros x y Exy.
    unfold tailT_. apply GFixR_unfold in Exy. destruct Exy as [Sxy Kxy].
    replace (GFix_out x) with (g_out x) in * by reflexivity.
    replace (GFix_out y) with (g_out y) in * by reflexivity.
    destruct (g_out x) as [sx kx], (g_out y) as [sy ky]. simpl in *.
    destruct sx as [ax tx], sy as [ay ty], Sxy as [_ Sxy]; simpl in *; trivial.
    constructor; trivial; simpl.
    intros [v1 V1] [v2 V2] Ev. simpl in *; subst. apply Kxy. trivial.
  Qed.
  Definition tailT := Eval unfold tailT_ in MkMorph tailT_morph.
End MemoTable.
Arguments Table {Sg}%type_scope {Esh} {Pg}%type_scope G A%type_scope {H}.
Arguments Cons & {Sg}%type_scope {Esh} {Pg}%type_scope {G} {A}%type_scope {_}.
Arguments headT {Sg}%type_scope {Esh} {Pg}%type_scope {G} {A}%type_scope {H}.
Arguments tailT {Sg}%type_scope {Esh} {Pg}%type_scope {G} {A}%type_scope {H}.

Definition dyna `{setoid A} `{setoid B} `{C : Cont Sc Pc}
  (a : App C (Table C A) ~> A) (c : RCoalg C B) : B ~> A
  := headT \o hylo (g_in \o Cons \o pair a id) c.

Definition NatF := Sum (K unit) Id.

Lemma valid_inr_tt : valid (Cont:=NatF) (inr tt, inr tt).
Proof. reflexivity. Qed.
Fixpoint lookupT_ (x : nat) (t : Table NatF int) {struct x}: option int :=
  match x with
  | 0 => Some (headT t)
  | S y =>
      match tailT t with
      | MkCont st kt =>
          match st with
          | inl tt => fun _ => None
          | inr tt => fun k => lookupT_ y (k (MkElem (inr tt) valid_inr_tt))
          end kt
      end
  end.

Lemma lookupT_morph
  : forall x y, x =e y -> lookupT_ (fst x) (snd x) =e lookupT_ (fst y) (snd y).
Proof.
  intros [x t] [y t'] [Exy Et]. simpl in *. subst. revert t t' Et.
  induction y as [|y Ih]; intros t t' Rt.
  - simpl in *. apply GFixR_unfold in Rt. destruct Rt as [St Kt].
    revert St Kt. replace (GFix_out t) with (g_out t) in * by reflexivity.
    replace (GFix_out t') with (g_out t') in * by reflexivity. intros St Kt.
    destruct (g_out t) as [[a st] kt], (g_out t') as [[b st'] kt']; simpl in *.
    destruct St;subst; trivial.
  - simpl. apply GFixR_unfold in Rt. revert Rt.
    replace (GFix_out t) with (g_out t) in * by reflexivity.
    replace (GFix_out t') with (g_out t') in * by reflexivity.
    destruct (g_out t) as [[a st] kt], (g_out t') as [[b st'] kt']; simpl in *.
    intros [[Sab St] Kt].
    destruct st as [[]|[]], st' as [[]|[]];
      try discriminate; try destruct St; trivial.
    subst. apply Ih, Kt. trivial.
Qed.

Definition lookupT : nat * Table NatF int ~> option int
  := MkMorph lookupT_morph.

Definition lookup_memo : Ext lookupT.
  calculate.
unfold lookupT, lookupT_.
simpl.
reflexivity.
Defined.

Definition out_nat : nat ~> App NatF nat.
|{ n ~>
  match n with
  | 0 => MkCont (inl tt) (fun e => 0)
  | S n => MkCont (inr tt) (fun _ => n)
  end
}|.
Defined.

Lemma out_nat_rec : RecP out_nat.
intros x; induction x as  [|x Ih]; constructor; trivial.
simpl. intros [[[]|]V]. simpl in V. discriminate.
Qed.
Canonical Structure out_natR := Rec out_nat_rec.

Fixpoint max_int acc (l : list int) :=
  match l with
  | h :: t =>
      if (acc <? h)%sint63 then max_int h t
      else max_int acc t
  | nil => acc
  end.

Fixpoint memo_knapsack table wvs :=
  match wvs with
  | nil => nil
  | h :: t =>
      match target lookup_memo (Nat.pred (fst h), table) with
      | Some u => (u + snd h)%sint63 :: memo_knapsack table t
      | None => memo_knapsack table t
      end
  end.

Lemma memo_knapsack_morph wvs :
  forall t1 t2, GFixR t1 t2 -> memo_knapsack t1 wvs = memo_knapsack t2 wvs.
Proof.
  intros t1 t2 Rt.
  (* Opaque lookupT lookupT_. *)
  induction wvs; simpl; trivial.
  destruct a as [n i]; simpl.
  assert (RWt : lookupT (Nat.pred n, t1) =e lookupT (Nat.pred n, t2))
    by (apply app_eq; simpl; split; trivial).
  simpl. rewrite RWt. clear RWt Rt. unfold lookupT, lookupT_. simpl.
  destruct (lookupT_ _); simpl; try rewrite IHwvs; reflexivity.
  (* Transparent lookupT lookupT_. *)
Qed.

Definition knapsack_alg (wvs : list (nat * int))
  (x : App NatF (Table NatF int)) : int
  := match x with
     | MkCont sx kx =>
         match sx with
         | inl tt => fun kx => 0%sint63
         | inr tt =>
             fun kx =>
               let table := kx (MkElem (inr tt) valid_inr_tt) in
               max_int 0 (memo_knapsack table wvs)
         end kx
     end.
Lemma knapsack_alg_morph wvs
  : forall x y, x =e y -> knapsack_alg wvs x =e knapsack_alg wvs y.
Proof.
  intros [sx kx] [sy ky] [Es Ek]. simpl in *.
  destruct sx as [[]|[]], sy as [[]|[]]; try destruct Es; trivial.
  assert (RR : GFixR (kx (MkElem (inr tt) valid_inr_tt))
                 (ky (MkElem (inr tt) valid_inr_tt)))
    by (apply Ek; trivial).
  rewrite (memo_knapsack_morph wvs RR).
  reflexivity.
Qed.

Definition knapsackA (wvs : list (nat * int))
  : App NatF (Table NatF int) ~> int
  := Eval unfold knapsack_alg in MkMorph (knapsack_alg_morph wvs).

Example ex1 wvs : Ext (dyna (knapsackA wvs) out_nat).
calculate.
unfold dyna, headT, fst, g_in, Cons, pair, out_nat, knapsackA.
simpl.
reflexivity.
Defined.

Module ToExtract.
  Definition knapsack := Eval unfold ex1 in ex1.
End ToExtract.

Extraction Inline app.
Set Extraction Flag 2047.
Recursive Extraction ToExtract.
