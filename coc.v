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

Reserved Notation "f ∘ g" (at level 30).

Inductive tm: Type :=
| var (x: string)

| set
| type

| all (x: string) (s: tm) (e: tm)
| lam (x: string) (s: tm) (e: tm)
| app (f x: tm)
.

Arguments tm: clear implicits.

Definition tm_eq (x y: tm): {x = y} + {x ≠ y}.
Proof.
  set (s := string_dec).
  decide equality.
Defined.


Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Function subst (x: string) (s: tm) (ev: tm): tm :=
  match ev with
  | var y =>
    if string_dec x y then s else ev

  | all y τ e =>
    if string_dec x y
    then
      ev
    else
      all y (subst x s τ) (subst x s e)
  | lam y τ e =>
    if string_dec x y
    then
      lam y (subst x s τ) e
    else
      lam y (subst x s τ) (subst x s e)

  | app e0 e1 => app (subst x s e0) (subst x s e1)

  | set => set
  | type => type
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) .


Definition ctx := list (string * tm).

Inductive maps: ctx → string → tm → Prop :=
| maps_head {Γ x τ}: maps ((x, τ) :: Γ) x τ
| maps_tail {Γ x y τ τ0}:
    y ≠ x →
    maps Γ x τ →
    maps ((y, τ0) :: Γ) x τ
.

Reserved Notation "Γ ⊢ e0 ▹ e1" (at level 80).
Reserved Notation "Γ ⊢ e ∈ τ" (at level 80).

(* FIXME *)
Inductive convertable (Γ: ctx): relation tm :=
| reflexive: reflexive tm (convertable Γ)
| transitive: transitive tm (convertable Γ)

(* FIXME enforce fresh vars ? *)
(* FIXME enforce maps ? *)
| alpha_conversion {x y e}: Γ ⊢ e ▹ [x := y] e

| beta_reduction {x t T u}: Γ ⊢ app (lam x T t) u ▹ [x := u] t
| eta_expansion {x t T}:
    Γ ⊢ t ▹ all x T (app t (var x))
where "Γ ⊢ e0 ▹ e1" := (convertable Γ e0 e1).

Instance convertable_PreOrder Γ: PreOrder (convertable Γ).
Proof.
  exists.
  - intros ?.
    apply reflexive.
  - intros ? ? ? p q.
    apply (transitive _ _ _ _ p).
    assumption.
Qed.

Definition definitionally_equal (Γ: ctx): relation tm :=
  λ e0 e1,
  ∃ u,
    (* FIXME, Not quite right *)
    Γ ⊢ e0 ▹ u ∧ Γ ⊢ e1 ▹ u.

Notation "Γ ⊢ e0 = e1" := (definitionally_equal Γ e0 e1) (at level 80).

Inductive judge (Γ: ctx): tm → tm → Type :=
| judge_var {x τ}:
    maps Γ x τ →
    Γ ⊢ var x ∈ τ

| judge_set:
    Γ ⊢ set ∈ type

| judge_all {x A B K L}:
    Γ ⊢ A ∈ K → (x, A) :: Γ ⊢ B ∈ L →
    Γ ⊢ all x A B ∈ L
| judge_lam {x A B K N}:
    Γ ⊢ A ∈ K → (x, A) :: Γ ⊢ N ∈ B →
    Γ ⊢ lam x A N ∈ (all x A B)
| judge_app {M N A B x}:
    Γ ⊢ M ∈ (all x A B) → Γ ⊢ N ∈ A →
    Γ ⊢ app M N ∈ [x:=N]B

(* | judge_convert {M A B K}: *)
(*     Γ ⊢ M ∈ A → Γ ⊢ A ▹ B → Γ ⊢ B ∈ K → *)
(*     Γ ⊢ M ∈ B *)
where "Γ ⊢ e ∈ τ" := (judge Γ e τ).

Reserved Notation "t '~>' t'" (at level 40).

Record ofty (τ: tm) := {
  term: tm ;
  proof: nil ⊢ term ∈ τ ;
}.

Arguments term {τ}.
Arguments proof {τ}.
Coercion term: ofty >-> tm.

Function lookup (Γ: ctx) (x:string) :=
  match Γ with
  | (y, τ) :: Γ' =>
    if string_dec y x then Some τ else lookup Γ' x
  | _ => None
  end.

Theorem lookup_complete {Γ x τ}:
  maps Γ x τ →
  lookup Γ x = Some τ.
Proof.
  intro p.
  induction p.
  - cbn in *.
    destruct (string_dec x x).
    2: contradiction.
    reflexivity.
  - cbn in *.
    destruct (string_dec y x).
    + subst.
      contradiction.
    + assumption.
Qed.

Theorem lookup_sound {Γ x τ}:
  lookup Γ x = Some τ →
  maps Γ x τ.
Proof.
  intro p.
  functional induction (lookup Γ x).
  all: inversion p.
  all: subst.
  all: constructor.
  all: auto.
Defined.

Function infer (Γ: ctx) (e: tm): option tm :=
  match e with
  | type => None

  | set => Some type

  | var x => lookup Γ x

  | all x A B =>
    if infer Γ A is Some K
    then
      if infer ((x, A) :: Γ) B is Some L
      then
        Some L
      else
        None
    else
      None

  | lam x A N =>
    if infer Γ A is Some K
    then
      if infer ((x, A) :: Γ) N is Some B
      then
        Some (all x A B)
      else
        None
    else
      None

  | app M N =>
    if infer Γ M is Some (all x A B)
    then
      if infer Γ N is Some A'
      then
        if tm_eq A A'
        then
          Some ([x := N] B)
        else
          None
      else
        None
    else
      None
  end.

Theorem infer_complete {Γ e τ}:
  Γ ⊢ e ∈ τ →
  infer Γ e = Some τ.
  intro p.
  induction p.
  - cbn.
    rewrite (lookup_complete m).
    reflexivity.
  - cbn.
    reflexivity.
  - cbn in *.
    rewrite IHp1, IHp2.
    cbn.
    reflexivity.
  - cbn in *.
    rewrite IHp1, IHp2.
    cbn.
    reflexivity.
  - cbn in *.
    rewrite IHp1, IHp2.
    cbn.
    destruct (tm_eq A A).
    2: contradiction.
    cbn.
    reflexivity.
Qed.

Theorem infer_sound {Γ e τ}:
  infer Γ e = Some τ → Γ ⊢ e ∈ τ.
Proof.
  generalize dependent τ.
  functional induction (infer Γ e).
  all: intros τ.
  all: intros p.
  all: try discriminate.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
  apply lookup_sound.
  auto.
Defined.

Definition typed (e: tm): if infer [] e is Some τ then ofty τ else True.
Proof.
  destruct (infer [] e) eqn:q.
  - exists e.
    apply infer_sound.
    assumption.
  - apply I.
Defined.

Example tt_typed: ofty _ := typed (all "x" set (var "x")).
Example id_typed: ofty _ := typed (lam "A" set (lam "x" (var "A") (var "x"))).


Function eval (e: tm): option tm :=
  match e with
  | app (lam x _ e0) e1 => Some ([x := e1] e0)

  | app e0 e1 =>
    eval e0 >>= λ e0',
    Some (app e0' e1)

  | _ => None
  end.


Definition includes (Γ Δ: ctx): Prop :=
  ∀ x τ, maps Δ x τ → maps Γ x τ.

Notation "Γ ⊑ Δ" := (includes Γ Δ) (at level 90).

Instance include_refl: Reflexive includes.
Proof.
  intros ? ? ? ?.
  assumption.
Qed.

Instance include_trans: Transitive includes.
Proof.
  intros ? ? ? p q ? ? ?.
  unfold includes in *.
  apply p.
  apply q.
  auto.
Qed.

Theorem weakest {Γ: ctx}: Γ ⊑ nil.
Proof.
  intros ? ? p.
  inversion p.
Qed.

Close Scope string_scope.

Theorem weaken_judge {Γ Δ} {e: tm} {τ}:
    Γ ⊑ Δ →
    Δ ⊢ e ∈ τ → Γ ⊢ e ∈ τ.
Proof.
  intros p ty.
  generalize dependent Γ.
  induction ty.
  all: intros.
  all: econstructor.
  all: eauto.
  - apply IHty2.
    intros ? ? ?.
    apply lookup_sound.
    destruct (string_dec x x0) eqn:q.
    all: subst.
    + set (p' := lookup_complete H).
      cbn in *.
      rewrite q in *.
      assumption.
    + set (p' := lookup_complete H).
      cbn in *.
      rewrite q in *.
      apply lookup_complete.
      apply p.
      apply lookup_sound.
      assumption.
  - apply IHty2.
    intros ? ? ?.
    apply lookup_sound.
    cbn.
    destruct (string_dec x x0) eqn:q.
    all: subst.
    + set (p' := lookup_complete H).
      cbn in *.
      rewrite q in p'.
      assumption.
    + set (p' := lookup_complete H).
      cbn in *.
      rewrite q in p'.
      apply lookup_complete.
      apply p.
      apply lookup_sound.
      assumption.
Defined.

Variant whnf: tm → Type :=
| whnf_set: whnf set
| whnf_type: whnf type

| whnf_all x A B: whnf (all x A B)
| whnf_lam x τ e: whnf (lam x τ e)
.

Variant cd: tm → Type :=
| cd_app e0 e1: cd (app e0 e1)
.



Inductive step: tm → tm → Type :=
| step_app_lam x τ e0 e1:
    app (lam x τ e0) e1 ~> [x:=e1]e0

| step_app e0 e1 e0':
    e0 ~> e0' →
    app e0 e1 ~> app e0' e1
where "A '~>' B" := (step A B).
