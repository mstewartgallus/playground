Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import FunInd.
Require Import Recdef.

Import IfNotations.
Import ListNotations.
Open Scope string_scope.

Close Scope nat.

Reserved Notation "⟨ x , y , .. , z ⟩".

Definition option_bind {A B} (x: option A) (f: A → option B): option B :=
  if x is Some x' then f x' else None.
Infix ">>=" := option_bind (at level 30, right associativity).

Definition option_then {A B} (x: option A) (y: option B): option B :=
  if x is Some _ then y else None.

Infix ">>" := option_then (at level 30, right associativity).

Inductive tm: Type :=
| set
| type

| prod (A B: tm)
| pos (κ: string) (A: tm)
| eq (κ μ: string)

| fanout (e0 e1: tm)
| π1 (e: tm)
| π2 (e: tm)

| box (κ: string) (e: tm)
| join (κ: string) (e: tm)

| id (κ: string)
| J (e0 e1: tm)
.

Arguments tm: clear implicits.

Definition tm_eq (x y: tm): {x = y} + {x ≠ y}.
Proof.
  set (s := string_dec).
  decide equality.
Defined.

Infix "×" := prod (at level 50).

Notation "'◇' κ , A" := (pos κ A) (at level 200).
(* (* Like forall but I use box because ∀ is already taken *) *)
(* Notation "□ κ , A" := (nec κ A) (at level 200). *)
Infix "~" := eq (at level 90).

Notation "⟨ x , y , .. , z ⟩" := (fanout .. (fanout x y) .. z).

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Function subst (x: string) (s: string) (ev: tm): tm :=
  match ev with
  | fanout e0 e1 => fanout (subst x s e0) (subst x s e1)
  | π1 e => π1 (subst x s e)
  | π2 e => π2 (subst x s e)

  | box κ e =>
    box (if string_dec x κ then s else κ) (subst x s e)
  | join κ e =>
    join (if string_dec x κ then s else κ) (subst x s e)

  | id κ => id (if string_dec x κ then s else κ)
  | J e0 e1 => J (subst x s e0) (subst x s e1)

  | prod e0 e1 => prod (subst x s e0) (subst x s e1)

  | (◇ κ, e) =>
    ◇ (if string_dec x κ then s else κ), subst x s e
  | (κ ~ μ) =>
    (if string_dec x κ then s else κ) ~ (if string_dec x μ then s else x)

  | set => set
  | type => type
  end.


Notation "'[' x ':=' s ']' t" := (subst x s t) .

Reserved Notation "e ∈ τ" (at level 80).

Inductive tm_equiv: relation tm :=
| reflexive: reflexive tm tm_equiv
| symmetric: symmetric tm tm_equiv
| transitive: transitive tm tm_equiv

| π1_fanout A B: tm_equiv (π1 (fanout A B)) A
| π2_fanout A B: tm_equiv (π2 (fanout A B)) B
.

Instance tm_Equivalence: Equivalence tm_equiv.
Proof.
  exists.
  - intros ?.
    apply reflexive.
  - intros ? ? ?.
    apply symmetric.
    assumption.
  - intros ? ? ? p q.
    apply (transitive _ _ _ p).
    assumption.
Qed.

Instance tm_Setoid: Setoid tm := {
  equiv := tm_equiv ;
}.

Inductive judge: tm → tm → Type :=
| judge_set:
    set ∈ type

| judge_prod {A B}:
    A ∈ set → B ∈ set →
    prod A B ∈ set
| judge_eq {κ μ}:
    (κ ~ μ) ∈ set
| judge_pos {κ A}:
    A ∈ set →
    (◇ κ, A) ∈ set

| judge_fanout {e0 e1 A B}:
    e0 ∈ A → e1 ∈ B →
    fanout e0 e1 ∈ (A × B)
| judge_π1 {e A B}:
    e ∈ A × B →
    π1 e ∈ A
| judge_π2 {e A B}:
    e ∈ A × B →
    π2 e ∈ B

| judge_box {κ e A}:
    e ∈ A →
    box κ e ∈ ◇ κ, A
| judge_join {κ e A}:
    e ∈ (◇ κ, (◇ κ, A)) →
    join κ e ∈ ◇ κ, A

| judge_id {κ}:
    id κ ∈ (κ ~ κ)

(* really unsure here *)
| judge_J {κ0 κ1 e0 e1 τ}:
    e0 ∈ (κ0 ~ κ1) →
    e1 ∈ (◇ κ0, τ) →
    J e0 e1 ∈ (◇ κ1, [κ0 := κ1]τ)

(* | judge_convert {M A B K}: *)
(*     M ∈ A → A == B → B ∈ K → *)
(*     M ∈ B *)
where "e ∈ τ" := (judge e τ).

Record ofty (τ: tm) := {
  term: tm ;
  proof: term ∈ τ ;
}.

Arguments term {τ}.
Arguments proof {τ}.
Coercion term: ofty >-> tm.

Function step (ev: tm): tm :=
  match ev with
  | π1 (fanout A _) => step A
  | π2 (fanout _ B) => step B

  | join _ (box _ (box κ e)) => box κ (step e)

  | J (id κ0) (box κ1 e1) => [κ1 := κ0] (step e1)

  | prod A B => prod (step A) (step B)
  | (◇ κ, A) => ◇ κ, step A
  | ⟨ e0 , e1 ⟩ => ⟨ step e0 , step e1 ⟩
  | π1 e => π1 (step e)
  | π2 e => π2 (step e)
  | box κ e => box κ (step e)
  | join κ e => join κ (step e)
  | J e0 e1 => J (step e0) (step e1)

  | _ => ev
  end.

Function infer (e: tm): option tm :=
  match e with
  | type => None

  | set => Some type

  | prod A B =>
    if infer A is Some set
    then
      if infer B is Some set
      then
        Some set
      else
        None
    else
      None
  | (◇ _, A) =>
    if infer A is Some set
    then
      Some set
    else
      None
  | (_ ~ _) => Some set

  | ⟨ e0 , e1 ⟩ =>
    if infer e0 is Some τ0
    then
      if infer e1 is Some τ1
      then
        Some (τ0 × τ1)
      else
        None
    else
      None
  | π1 e =>
    if infer e is Some (τ0 × τ1)
    then Some τ0
    else None
  | π2 e =>
    if infer e is Some (τ0 × τ1)
    then Some τ1
    else None

  | box κ e =>
    if infer e is Some τ
    then
      Some (◇ κ, τ)
    else
      None
  | join κ e =>
    if infer e is Some (◇ κ0, ◇ κ1, A)
    then
      if string_dec κ κ0
      then
        if string_dec κ κ1
        then
          Some (◇ κ, A)
        else
          None
      else
        None
    else
      None

  | id κ => Some (κ ~ κ)
  | J e0 e1 =>
    if infer e0 is Some (κ0 ~ κ1)
    then
      if infer e1 is Some (◇ κ0', τ)
      then
        if string_dec κ0 κ0'
        then
          Some (◇ κ1, [κ0 := κ1] τ)
        else
          None
      else
        None
    else
      None
  end.

Theorem infer_complete {e τ}:
  e ∈ τ →
  infer e = Some τ.
  intro p.
  induction p.
  all: cbn.
  all: try reflexivity.
  - rewrite IHp1, IHp2.
    cbn.
    reflexivity.
  - cbn.
    rewrite IHp.
    reflexivity.
  - cbn.
    rewrite IHp1, IHp2.
    cbn.
    reflexivity.
  - cbn.
    rewrite IHp.
    reflexivity.
  - cbn.
    rewrite IHp.
    reflexivity.
  - cbn.
    rewrite IHp.
    reflexivity.
  - cbn.
    rewrite IHp.
    destruct (string_dec κ κ).
    2:contradiction.
    reflexivity.
  - cbn.
    rewrite IHp1, IHp2.
    cbn.
    destruct (string_dec κ0 κ0).
    2: contradiction.
    cbn.
    reflexivity.
Qed.

Theorem infer_sound {e τ}:
  infer e = Some τ → e ∈ τ.
Proof.
  generalize dependent τ.
  functional induction (infer e).
  all: intros τ'.
  all: intros p.
  all: try discriminate.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
Defined.

Definition typed (e: tm): if infer e is Some τ then ofty τ else True.
Proof.
  destruct (infer e) eqn:q.
  - exists e.
    apply infer_sound.
    assumption.
  - apply I.
Defined.

Example tt_typed: ofty _ :=
  typed
    (J (id "x") (box "x" (◇ "x", "x" ~ "x"))).
