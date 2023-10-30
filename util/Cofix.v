Require Export ssreflect.
Require Import Paco.paco.

Ltac done :=
  eauto; hnf; intros; solve
   [ do ![solve [eauto | apply: sym_equal; eauto]
         | discriminate | contradiction | split]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; eauto] end ].

Inductive _co_marker := _co_marker_constr.

Ltac co_move :=
  let M := fresh "M" in
  move: _co_marker_constr => M;
  repeat
    match goal with
    | [|- forall nm : ?P, _] =>
      let H := fresh nm in
      move=> H
    end
.

Ltac co_revert :=
  match goal with
  | [x : ?T |- _] =>
    match T with
    | _co_marker => move=>{x}
    | _ => move: x; co_revert
    end
  end.

Ltac pack :=
    match goal with
    | [ x : ?T, y : ?T1 |- ?P ] =>
        match T with
        | _co_marker => move: {x} y
        | _ => move: {x y} (ex_intro (fun x => _) x y) => x; pack
        end
    end.

Ltac float_hyp H :=
  match goal with
  | [x : ?T |- forall a : ?P, _] =>
    (* let H := fresh a in *)
    match T with
    | _co_marker =>
      move=> H {x}; co_move
    | _ =>
      move=> H; move: H x; float_hyp H
    end
  end.

Ltac add_equalities :=
  repeat
    match goal with
    | [|- context [ ?P (?f ?x) ]] =>
        let Hf := fresh "f" in
        move: {-1}(f x) (@eq_refl _ (f x)); float_hyp Hf
    | [|- context [ ?P ?x ?x ]] =>
        let y := fresh "x" in
      move: {1 3}x (@eq_refl _ x); float_hyp y
    end.

Ltac co_gen :=
  repeat
    match goal with
    | [|- ?P -> ?Q ?x] => move: x
    | [x : ?A|- forall y, ?P -> ?Q ?x y] => move: x
    end.

Ltac simpl_ch CH :=
  move: CH;
  repeat
    match goal with
    | [|- forall x : ?A, _] =>
      match A with
      | (forall a, (exists _, _) -> _) => move=>/(_ _ (ex_intro _ _ _))
      | (forall a b, (exists _, _) -> _) => move=>/(_ _ _ (ex_intro _ _ _))
      | (forall a b c, (exists _, _) -> _) => move=>/(_ _ _ _ (ex_intro _ _ _))
      | (forall a b c d, (exists _, _) -> _) => move=>/(_ _ _ _ _ (ex_intro _ _ _))
      | (forall a b c d e, (exists _, _) -> _) => move=>/(_ _ _ _ _ _ (ex_intro _ _ _))
      | (forall a b c d e f, (exists _, _) -> _) => move=>/(_ _ _ _ _ _ _ (ex_intro _ _ _))
      | (forall a,           _ /\ _ -> _) => move=>/(_ _           (conj _ _))
      | (forall a b,         _ /\ _ -> _) => move=>/(_ _ _         (conj _ _))
      | (forall a b c,       _ /\ _ -> _) => move=>/(_ _ _ _       (conj _ _))
      | (forall a b c d,     _ /\ _ -> _) => move=>/(_ _ _ _ _     (conj _ _))
      | (forall a b c d e  , _ /\ _ -> _) => move=>/(_ _ _ _ _ _   (conj _ _))
      | (forall a b c d e f, _ /\ _ -> _) => move=>/(_ _ _ _ _ _ _ (conj _ _))
      | (forall a,           _ = _ -> _) => move=>/(_ _           eq_refl)
      | (forall a b,         _ = _ -> _) => move=>/(_ _ _         eq_refl)
      | (forall a b c,       _ = _ -> _) => move=>/(_ _ _ _       eq_refl)
      | (forall a b c d,     _ = _ -> _) => move=>/(_ _ _ _ _     eq_refl)
      | (forall a b c d e  , _ = _ -> _) => move=>/(_ _ _ _ _ _   eq_refl)
      | (forall a b c d e f, _ = _ -> _) => move=>/(_ _ _ _ _ _ _ eq_refl)
      end
    end.

Ltac cleanup :=
  let X := fresh "M" in
  move: _co_marker_constr=>X;
  repeat
    match goal with
    | [|- forall a : ?T, _] =>
      let X := fresh a in
      match T with
      | _ /\ _ => case
      | exists _, _ => case
      | ?x = _ => move=>->{x}
      | _ = ?x => move=><-{x}
      | _ => move=> X
      end
    end.

Ltac cleanup_ch_ex CH :=
  repeat (
      try move: CH =>/(_ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ _ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@ex_intro _ _ _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@ex_intro _ _ _ _))-CH
    ).

Ltac cleanup_ch_eq CH :=
  repeat (
      try move: CH =>/(_ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ _ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@eq_refl _ _))-CH;
      try move: CH =>/(_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@eq_refl _ _))-CH
    ).

Ltac post_coind CH :=
  let r := fresh "r" in
  let b := fresh "bot" in
  let ch := fresh "CH" in
  intros r _ CH; cleanup; cleanup_ch_ex CH; cleanup_ch_eq CH; revert CH;
  float_hyp CH; co_revert.

Ltac pre_coind :=
  co_move; add_equalities; pack; co_gen.


Ltac coind CH :=
  pre_coind;
  match goal with
  | [|- _] => apply/paco1_acc
  | [|- _] => apply/paco2_acc
  | [|- _] => apply/paco3_acc
  | [|- _] => apply/paco4_acc
  | [|- _] => apply/paco5_acc
  end;
  post_coind CH.
