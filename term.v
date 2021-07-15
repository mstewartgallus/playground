Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Coq.Structures.OrdersAlt.
Require Coq.Structures.OrderedTypeEx.
Require Coq.MSets.MSetAVL.
Require Coq.MSets.MSetInterface.
Require Coq.FSets.FMapList.

Import IfNotations.
Import ListNotations.
Open Scope string_scope.

Close Scope nat.

Module F := FMapList.Make OrderedTypeEx.String_as_OT.

Reserved Notation "⟨ x , y , .. , z ⟩".

Reserved Notation "'some' x .. y , P"
         (at level 200, x binder, y binder, right associativity,
          format "'[ ' '[ ' 'some'  x .. y ']' ,  '/' P ']'").
Reserved Notation "'Σ' x .. y , P"
         (at level 200, x binder, y binder, right associativity,
          format "'[ ' '[ ' 'Σ'  x .. y ']' ,  '/' P ']'").

Record someT [A] (P: A → Type) := some_intro { head: A ; tail: P head ; }.

Arguments some_intro [A P].
Arguments head [A P].
Arguments tail [A P].

Module Import SomeNotations.
  Add Printing Let someT.

  Notation "'some' x .. y , P" := (someT (λ x, .. (someT (λ y,  P)) .. )) : type_scope.
  Notation "'Σ' x .. y , P" := (someT (λ x, .. (someT (λ y,  P)) .. )) : type_scope.
  Notation "⟨ x , y , .. , z ⟩" := (some_intro .. (some_intro x y) .. z) : core_scope.
End SomeNotations.

Definition option_bind {A B} (x: option A) (f: A → option B): option B :=
  if x is Some x' then f x' else None.
Infix ">>=" := option_bind (at level 30, right associativity).

Definition option_then {A B} (x: option A) (y: option B): option B :=
  if x is Some _ then y else None.

Infix ">>" := option_then (at level 30, right associativity).

Inductive sort :=
| unit
| prod (A B: sort)
| exp (s t: sort)
| pos (κ: string) (A: sort)
| nec (κ: string) (A: sort)
| eq (κ μ: string).

Notation "[ A , B ]" := (exp A B).
Infix "×" := prod (at level 50).

Notation "'◇' κ , A" := (pos κ A) (at level 200).
(* Like forall but I use box because ∀ is already taken *)
Notation "□ κ , A" := (nec κ A) (at level 200).
Infix "~" := eq (at level 90).

Reserved Notation "f ∘ g" (at level 30).

Definition sort_eq (x y: sort): {x = y} + {x ≠ y}.
Proof.
  set (s := string_dec).
  decide equality.
Defined.

(* Strings are really dumb but I don't want to figure out two things
at the same time *)

Inductive tm: Type :=
| var (x: string)

| lam (x: string) (s: sort) (e: tm)
| app (f x: tm)

| tt

| fanout (e0 e1: tm)
| π1 (e: tm)
| π2 (e: tm)

| necessity (κ: string) (e: tm)

| ext (κ: string) (e: tm)
| dup (e: tm)

| box (κ: string) (e: tm)
| bind (e0: tm) (x: string) (e1: tm)

| id (κ: string)
| compose (e0 e1: tm)
| sym (e: tm)

| cast_pos (e0 e1: tm)
| cast_nec (e0 e1: tm)
.

Arguments tm: clear implicits.

Infix "∘" := compose.

Definition ctx := string → option sort.
Definition mt: ctx := λ _, None.
Definition add x τ (m: ctx): ctx := λ y, if string_dec x y then Some τ else m y.

Theorem add_add x τ0 τ1 (m: ctx): add x τ0 (add x τ1 m) = add x τ0 m.
Proof.
  extensionality y.
  unfold add.
  destruct (string_dec x y).
  all: reflexivity.
Qed.

Theorem add_comm x y τ0 τ1 (m: ctx):
  x ≠ y →
 add x τ0 (add y τ1 m) = add y τ1 (add x τ0 m).
Proof.
  intro p.
  extensionality z.
  unfold add.
  destruct (string_dec x z), (string_dec y z).
  all: try reflexivity.
  subst.
  contradiction.
Qed.

Reserved Notation "Γ ⊢ e ∈ τ" (at level 80).

Inductive judge (Γ: ctx): tm → sort → Type :=
| judge_var x τ:
    Γ x = Some τ →
    Γ ⊢ var x ∈ τ

| judge_tt:
    Γ ⊢ tt ∈ unit
| judge_fanout e0 e1 τ0 τ1:
    Γ ⊢ e0 ∈ τ0 → Γ ⊢ e1 ∈ τ1 →
    Γ ⊢ fanout e0 e1 ∈ (τ0 × τ1)

| judge_π1 e τ0 τ1:
    Γ ⊢ e ∈ (τ0 × τ1) →
    Γ ⊢ π1 e ∈ τ0
| judge_π2 e τ0 τ1:
    Γ ⊢ e ∈ (τ0 × τ1) →
    Γ ⊢ π2 e ∈ τ1

| judge_lam e τ0 τ1 x:
    add x τ0 Γ ⊢ e ∈ τ1 →
    Γ ⊢ lam x τ0 e ∈ [τ0, τ1]
| judge_app e0 e1 τ0 τ1:
    Γ ⊢ e0 ∈ [τ0, τ1] → Γ ⊢ e1 ∈ τ0 →
    Γ ⊢ app e0 e1 ∈ τ1

| judge_necessity κ e τ:
    mt ⊢ e ∈ τ →
    Γ ⊢ necessity κ e ∈ (□ κ, τ)

| judge_ext κ e τ:
    Γ ⊢ e ∈ (□ κ, τ) →
    Γ ⊢ ext κ e ∈ τ
| judge_dup κ e τ:
    Γ ⊢ e ∈ (□ κ, τ) →
    Γ ⊢ dup e ∈ (□ κ, □ κ, τ)

| judge_box κ e τ:
    Γ ⊢ e ∈ τ →
    Γ ⊢ box κ e ∈ (◇ κ, τ)

| judge_bind e0 e1 x κ τ0 τ1:
    Γ ⊢ e0 ∈ (◇ κ, τ0) → add x τ0 Γ ⊢ e1 ∈ (◇ κ, τ1) →
    Γ ⊢ bind e0 x e1 ∈ (◇ κ, τ1)

| judge_id κ:
    Γ ⊢ id κ ∈ (κ ~ κ)

| judge_compose e0 e1 κ0 κ1 κ2:
    Γ ⊢ e0 ∈ (κ1 ~ κ2) → Γ ⊢ e1 ∈ (κ0 ~ κ1) →
    Γ ⊢ (e0 ∘ e1) ∈ (κ0 ~ κ2)

| judge_sym e κ0 κ1:
    Γ ⊢ e ∈ (κ1 ~ κ0) →
    Γ ⊢ sym e ∈ (κ0 ~ κ1)

(* Really unsure of these as faithful to cylindrical logic *)
| judge_cast_pos e0 e1 κ0 κ1 τ:
      Γ ⊢ e0 ∈ (κ0 ~ κ1) → Γ ⊢ e1 ∈ (◇ κ0, τ) →
      Γ ⊢ cast_pos e0 e1 ∈ (◇ κ1, τ)
| judge_cast_nec e0 e1 κ0 κ1 τ:
    Γ ⊢ e0 ∈ (κ0 ~ κ1) →
    Γ ⊢ e1 ∈ (□ κ0, τ) →
    Γ ⊢ cast_nec e0 e1 ∈ (□ κ1, τ)
where "Γ ⊢ e ∈ τ" := (judge Γ e τ).

Record ofty (τ: sort) := {
  term: tm ;
  proof: mt ⊢ term ∈ τ ;
}.

Fixpoint infer (Γ: ctx) (e: tm): option sort :=
  match e with
  | var x => Γ x

  | lam x τ0 e =>
    infer (add x τ0 Γ) e >>= λ τ1,
    Some [τ0, τ1]

  | app e0 e1 =>
    infer Γ e0 >>= λ A,
    (if A is [τ0, τ1] then Some (τ0, τ1) else None) >>= λ '(τ0, τ1),
    infer Γ e1 >>= λ τ0',
    (if sort_eq τ0 τ0' then Some tt else None) >>
    Some τ1

  | tt => Some unit

  | fanout e0 e1 =>
    infer Γ e0 >>= λ τ0,
    infer Γ e1 >>= λ τ1,
    Some (τ0 × τ1)

  | π1 e =>
    infer Γ e >>= λ A,
    if A is (τ0 × τ1)
    then Some τ0
    else None

  | π2 e =>
    infer Γ e >>= λ A,
    if A is (τ0 × τ1)
    then Some τ1
    else None

  | necessity κ e =>
    infer mt e >>= λ τ,
    Some (□ κ, τ)

  | ext κ e =>
    infer Γ e >>= λ A,
    (if A is (□ κ', τ) then Some (κ', τ) else None) >>= λ '(κ', τ),
    (if string_dec κ κ' then Some tt else None) >>
    Some τ
  | dup e =>
    infer Γ e >>= λ A,
    (if A is (□ κ, τ) then Some (κ, τ) else None) >>= λ '(κ, τ),
    Some (□ κ, □ κ, τ)

  | box κ e =>
    infer Γ e >>= λ τ,
    Some (◇ κ, τ)

  | bind e0 x e1 =>
    infer Γ e0 >>= λ A,
    (if A is (◇ κ0, τ0) then Some (κ0, τ0) else None) >>= λ '(κ0, τ0),
    infer (add x τ0 Γ) e1 >>= λ B,
    (if B is (◇ κ1, τ1) then Some (κ1, τ1) else None) >>= λ '(κ1, τ1),
    (if string_dec κ0 κ1 then Some tt else None) >>
    Some (◇ κ1, τ1)

  | id κ => Some (κ ~ κ)
  | e0 ∘ e1 =>
    infer Γ e0 >>= λ A,
    infer Γ e1 >>= λ B,
    (if A is κ1 ~ κ2 then Some (κ1, κ2) else None) >>= λ '(κ1, κ2),
    (if B is κ0 ~ κ1' then Some (κ0, κ1') else None) >>= λ '(κ0, κ1'),
    (if string_dec κ1 κ1' then Some tt else None) >>
    Some (κ0 ~ κ2)

  | sym e =>
    infer Γ e >>= λ A,
    (if A is κ0 ~ κ1 then Some (κ0, κ1) else None) >>= λ '(κ0, κ1),
    Some (κ1 ~ κ0)

  | cast_pos e0 e1 =>
    infer Γ e0 >>= λ A,
    infer Γ e1 >>= λ B,
    (if A is κ0 ~ κ1 then Some (κ0, κ1) else None) >>= λ '(κ0, κ1),
    (if B is ◇ κ0', τ then Some (κ0', τ) else None) >>= λ '(κ0', τ),
    (if string_dec κ0 κ0' then Some tt else None) >>
    Some (◇ κ1, τ)

  | cast_nec e0 e1 =>
    infer Γ e0 >>= λ A,
    infer Γ e1 >>= λ B,
    (if A is κ0 ~ κ1 then Some (κ0, κ1) else None) >>= λ '(κ0, κ1),
    (if B is □ κ0', τ then Some (κ0', τ) else None) >>= λ '(κ0', τ),
    (if string_dec κ0 κ0' then Some tt else None) >>
    Some (□ κ1, τ)
  end.

Theorem infer_sound {Γ e τ}:
  infer Γ e = Some τ → Γ ⊢ e ∈ τ.
Proof.
  generalize dependent Γ.
  generalize dependent τ.
  induction e.
  all: intros τ Γ p.
  all: cbn in *.
  - apply judge_var.
    assumption.
  - destruct (infer (add x s Γ) e) eqn:q.
    2: discriminate.
    inversion p.
    subst.
    apply judge_lam.
    apply IHe.
    apply q.
  - destruct (infer Γ e1) eqn:q1.
    all: try discriminate.
    cbn in *.
    destruct s.
    all: try discriminate.
    cbn in *.
    destruct (infer Γ e2) eqn:q2.
    all: try discriminate.
    cbn in *.
    destruct (sort_eq s1 s).
    all: try discriminate.
    cbn in *.
    inversion p.
    subst.
    eapply judge_app.
    Unshelve.
    3: apply s.
    + apply IHe1.
      apply q1.
    + apply IHe2.
      apply q2.
  - inversion p.
    subst.
    apply judge_tt.
  - destruct (infer Γ e1) eqn:q1.
    all: try discriminate.
    destruct (infer Γ e2) eqn:q2.
    all: try discriminate.
    inversion p.
    subst.
    apply judge_fanout.
    + apply IHe1.
      assumption.
    + apply IHe2.
      assumption.
  - destruct (infer Γ e) eqn:q.
    all: try discriminate.
    destruct s.
    all: try discriminate.
    eapply judge_π1.
    Unshelve.
    2: apply s2.
    inversion p.
    subst.
    apply IHe.
    assumption.
  - destruct (infer Γ e) eqn:q.
    all: try discriminate.
    destruct s.
    all: try discriminate.
    eapply judge_π2.
    Unshelve.
    2: apply s1.
    inversion p.
    subst.
    apply IHe.
    assumption.
  - destruct (infer mt e) eqn:q.
    all: try discriminate.
    inversion p.
    subst.
    apply judge_necessity.
    apply IHe.
    assumption.
  - destruct (infer Γ e) eqn:q.
    all: try discriminate.
    cbn in *.
    destruct s.
    all: try discriminate.
    cbn in *.
    destruct (string_dec κ κ0).
    all: try discriminate.
    cbn in *.
    inversion p.
    subst.
    apply judge_ext.
    apply IHe.
    assumption.
  - destruct (infer Γ e) eqn:q.
    all: try discriminate.
    destruct s.
    all: try discriminate.
    inversion p.
    subst.
    apply judge_dup.
    apply IHe.
    assumption.
  - destruct (infer Γ e) eqn:q.
    all: try discriminate.
    inversion p.
    subst.
    apply judge_box.
    apply IHe.
    assumption.
  - destruct (infer Γ e1) eqn:q1.
    all: try discriminate.
    cbn in *.
    destruct s.
    all: try discriminate.
    cbn in *.
    destruct (infer (add x s Γ) e2) eqn:q2.
    all: try discriminate.
    cbn in *.
    destruct s0.
    all: try discriminate.
    cbn in *.
    destruct (string_dec κ κ0).
    all: try discriminate.
    cbn in *.
    inversion p.
    subst.
    eapply judge_bind.
    Unshelve.
    3: apply s.
    + apply IHe1.
      assumption.
    + apply IHe2.
      assumption.
  - inversion p.
    subst.
    apply judge_id.
  - destruct (infer Γ e1) eqn:q1.
    all: try discriminate.
    cbn in *.
    destruct (infer Γ e2) eqn:q2.
    all: try discriminate.
    cbn in *.
    destruct s.
    cbn in *.
    all: try discriminate.
    cbn in *.
    destruct s0.
    all: try discriminate.
    cbn in *.
    destruct (string_dec κ μ0).
    all: try discriminate.
    cbn in *.
    inversion p.
    subst.
    eapply judge_compose.
    Unshelve.
    3: apply μ0.
    + apply IHe1.
      assumption.
    + apply IHe2.
      assumption.
  - destruct (infer Γ e) eqn:q.
    all: try discriminate.
    cbn in *.
    destruct s.
    all: try discriminate.
    cbn in *.
    inversion p.
    subst.
    apply judge_sym.
    apply IHe.
    assumption.
  - destruct (infer Γ e1) eqn:q1.
    all: try discriminate.
    cbn in *.
    destruct (infer Γ e2) eqn:q2.
    all: try discriminate.
    cbn in *.
    destruct s.
    all: try discriminate.
    cbn in *.
    destruct s0.
    all: try discriminate.
    cbn in *.
    destruct (string_dec κ κ0).
    all: try discriminate.
    cbn in *.
    inversion p.
    subst.
    eapply judge_cast_pos.
    Unshelve.
    3: apply κ0.
    + apply IHe1.
      assumption.
    + apply IHe2.
      assumption.
  - destruct (infer Γ e1) eqn:q1.
    all: try discriminate.
    cbn in *.
    destruct (infer Γ e2) eqn:q2.
    all: try discriminate.
    cbn in *.
    destruct s.
    all: try discriminate.
    cbn in *.
    destruct s0.
    all: try discriminate.
    cbn in *.
    destruct (string_dec κ κ0).
    all: try discriminate.
    inversion p.
    subst.
    eapply judge_cast_nec.
    Unshelve.
    3: apply κ0.
    + apply IHe1.
      assumption.
    + apply IHe2.
      assumption.
Defined.

Theorem infer_complete {Γ e τ}:
  Γ ⊢ e ∈ τ → infer Γ e = Some τ.
  intro p.
  induction p.
  all: cbn in *.
  all: auto.
  all: try rewrite IHp.
  all: cbn in *.
  all: try rewrite IHp1.
  all: cbn in *.
  all: try rewrite IHp2.
  all: cbn in *.
  all: try reflexivity.
  all: cbn in *.
  - destruct (sort_eq τ0 τ0).
    2: contradiction.
    reflexivity.
  - destruct (string_dec κ κ).
    2: contradiction.
    reflexivity.
  - destruct (string_dec κ κ).
    2: contradiction.
    reflexivity.
  - destruct (string_dec κ1 κ1).
    2: contradiction.
    reflexivity.
  - destruct (string_dec κ0 κ0).
    2: contradiction.
    reflexivity.
  - destruct (string_dec κ0 κ0).
    2: contradiction.
    reflexivity.
Qed.

Definition typed (e: tm): if infer mt e is Some τ then ofty τ else True.
Proof.
  destruct (infer mt e) eqn:q.
  - exists e.
    apply infer_sound.
    assumption.
  - apply I.
Defined.

Example tt_typed: ofty unit := typed tt.
Example id_typed A: ofty (exp A A) := typed (lam "x" A (var "x")).
Example compose_typed: ofty _ := typed (id "κ" ∘ id "κ").
Example id_tt: ofty _ := typed (app (lam "x" unit (var "x")) tt).

Definition includes (Γ Δ: ctx): Prop :=
  ∀ x τ, Δ x = Some τ → Γ x = Some τ.

Notation "Γ ⊑ Δ" := (includes Γ Δ) (at level 90).

Instance include_refl: Reflexive includes.
Proof.
  intros ? ? ? ?.
  auto.
Qed.

Instance include_trans: Transitive includes.
Proof.
  intros ? ? ? p q ? ? ?.
  unfold includes in p, q.
  apply p.
  apply q.
  auto.
Qed.

Theorem weakest {Γ: ctx}: Γ ⊑ mt.
Proof.
  intros ? ? ?.
  discriminate.
Qed.

Theorem weaken {Γ Δ} {e: tm} {τ}:
    Γ ⊑ Δ →
    Δ ⊢ e ∈ τ → Γ ⊢ e ∈ τ.
Proof.
  intros p ty.
  generalize dependent Γ.
  induction ty.
  all: intros.
  all: econstructor.
  all: eauto.
  - apply IHty.
    unfold add.
    intros ? ? ?.
    destruct (string_dec x x0).
    all: auto.
  - apply IHty2.
    unfold add.
    intros ? ? ?.
    destruct (string_dec x x0).
    all: auto.
Qed.

Variant whnf: tm → Type :=
| whnf_tt: whnf tt
| whnf_fanout e0 e1: whnf (fanout e0 e1)
| whnf_lam x τ e: whnf (lam x τ e)
| whnf_box κ e: whnf (box κ e)
| whnf_nec κ e: whnf (necessity κ e)
| whnf_id κ: whnf (id κ)
.

Variant cd: tm → Type :=
| cd_app e0 e1: cd (app e0 e1)
| cd_π1 e: cd (π1 e)
| cd_π2 e: cd (π2 e)
| cd_ext κ e: cd (ext κ e)
| cd_dup e: cd (dup e)
| cd_bind e0 x e1: cd (bind e0 x e1)
| cd_compose e0 e1: cd (e0 ∘ e1)
| cd_sym e: cd (sym e)
| cd_cast_pos e0 e1: cd (cast_pos e0 e1)
| cd_cast_nec e0 e1: cd (cast_nec e0 e1)
.

Lemma canonical {v: tm} {τ}:
  mt ⊢ v ∈ τ → whnf v →
  match τ with
  | unit => (v = tt: Type)
  | prod _ _ => Σ e0 e1, v = fanout e0 e1
  | exp τ0 _ => Σ x e0, v = lam x τ0 e0
  | pos κ _ => Σ e, v = box κ e
  | nec κ _ => Σ e, v = necessity κ e
  | eq κ0 κ1 => (κ0 = κ1) ∧ v = id κ0
  end.
Proof.
  intros p w.
  destruct τ.
  all: destruct w.
  all: inversion p.
  all: subst.
  all: eauto.
  - exists e0.
    exists e1.
    reflexivity.
  - exists x.
    exists e.
    reflexivity.
  - exists e.
    reflexivity.
  - exists e.
    reflexivity.
Defined.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Section subst.
  Context (x: string) (s: tm).
  Fixpoint subst (ev: tm): tm :=
    match ev with
    | var y => if string_dec x y then s else ev

    | lam y τ e => if string_dec x y then ev else lam y τ (subst e)
    | bind e0 y e1 =>
      bind (subst e0) y (if string_dec x y then e1 else subst e1)

    | tt => ev

    | app e0 e1 => app (subst e0) (subst e1)

    | fanout e0 e1 => fanout (subst e0) (subst e1)
    | π1 e => π1 (subst e)
    | π2 e => π2 (subst e)

    | necessity κ e => necessity κ (subst e)

    | ext κ e => ext κ (subst e)
    | dup e => dup (subst e)

    | box κ e => box κ (subst e)

    | id κ => id κ
    | e0 ∘ e1 =>  (subst e0) ∘ (subst e1)
    | sym e => sym (subst e)

    | cast_pos e0 e1 => cast_pos (subst e0) (subst e1)
    | cast_nec e0 e1 => cast_nec (subst e0) (subst e1)
    end.
End subst.

Notation "'[' x ':=' s ']' t" := (subst x s t) .

Theorem subst_type {Γ x} {e0 e1: tm} {τ0 τ1}:
  add x τ1 Γ ⊢ e0 ∈ τ0 →
  mt ⊢ e1 ∈ τ1 →
  Γ ⊢ [x:=e1]e0 ∈ τ0.
Proof.
  intros p q.
  generalize dependent Γ.
  generalize dependent τ0.
  induction e0.
  all: intros.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: try eauto.
  - cbn.
    destruct (string_dec x x0) eqn:r.
    + cbn in *.
      set (p' := infer_complete p).
      unfold add in p'.
      cbn in *.
      rewrite r in p'.
      cbn in *.
      inversion p'.
      subst.
      refine (weaken _ q).
      intros ? ? ?.
      unfold mt in *.
      discriminate.
    + cbn in *.
      set (p' := infer_complete p).
      unfold add in p'.
      cbn in *.
      rewrite r in p'.
      apply judge_var.
      auto.
  - cbn in *.
    destruct (string_dec x x0).
    + subst.
      apply judge_lam.
      rewrite add_add in H3.
      assumption.
    + apply judge_lam.
      apply IHe0.
      rewrite add_comm.
      1: assumption.
      assumption.
  - cbn.
    apply IHe0.
    refine (weaken _ H2).
    intros ? ? ?.
    unfold mt in *.
    discriminate.
  - cbn.
    destruct (string_dec x x0).
    + subst.
      rewrite add_add in H4.
      auto.
    + apply IHe0_2.
      rewrite add_comm in H4.
      2: auto.
      auto.
Qed.

Reserved Notation "t '~>' t'" (at level 40).

Inductive step: tm → tm → Type :=
| step_app_lam x τ e0 e1:
    app (lam x τ e0) e1 ~> [x:=e1]e0
| step_bind_box κ e0 x e1:
    bind (box κ e0) x e1 ~> [x:=e0]e1

| step_π1_fanout e0 e1:
    π1 (fanout e0 e1) ~> e0
| step_π2_fanout e0 e1:
    π2 (fanout e0 e1) ~> e1

| step_ext_necessity κ e:
    ext κ (necessity κ e) ~> e
| step_dup_necessity κ e:
    dup (necessity κ e) ~> necessity κ (necessity κ e)

| step_sym_id κ:
    sym (id κ) ~> id κ
| step_compose_id κ:
    id κ ∘ id κ ~> id κ

| step_cast_pos_id_box κ e:
    cast_pos (id κ) (box κ e) ~> box κ e
| step_cast_nec_id_box κ e:
    cast_nec (id κ) (necessity κ e) ~> necessity κ e

| step_bind e0 x e1 e0':
    e0 ~> e0' →
    bind e0 x e1 ~> bind e0' x e1

| step_app e0 e1 e0':
    e0 ~> e0' →
    app e0 e1 ~> app e0' e1
| step_π1 e e':
    e ~> e' →
    π1 e ~> π1 e'
| step_π2 e e':
    e ~> e' →
    π2 e ~> π2 e'

| step_ext κ e e':
    e ~> e' →
    ext κ e ~> ext κ e'
| step_dup e e':
     e ~> e' →
    dup e ~> dup e'

| step_compose_l e0 e0' e1:
    e0 ~> e0' →
    e0 ∘ e1 ~> e0' ∘ e1
| step_compose_r e0 e1 e1':
    e1 ~> e1' →
    e0 ∘ e1 ~> e0 ∘ e1'

| step_sym e e':
    e ~> e' →
    sym e ~> sym e'

| step_cast_pos_l e0 e1 e0':
    e0 ~> e0' →
    cast_pos e0 e1 ~> cast_pos e0' e1
| step_cast_pos_r e0 e1 e1':
    e1 ~> e1' →
    cast_pos e0 e1 ~> cast_pos e0 e1'

| step_cast_nec_l e0 e1 e0':
    e0 ~> e0' →
    cast_nec e0 e1 ~> cast_nec e0' e1
| step_cast_nec_r e0 e1 e1':
    e1 ~> e1' →
    cast_nec e0 e1 ~> cast_nec e0 e1'

where "A '~>' B" := (step A B).

Lemma to_cd {e e': tm}: e ~> e' → cd e.
Proof.
  intro s.
  induction s.
  all: constructor.
Defined.

Theorem progress (e: tm) {τ}:
  mt ⊢ e ∈ τ →
  whnf e + (Σ e', e ~> e').
Proof.
  remember mt as Γ.
  intro p.
  induction p.
  all: subst.
  all: try discriminate.
  all: try (left; constructor).
  all: try destruct (IHp eq_refl).
  all: try destruct (IHp1 eq_refl).
  all: try destruct (IHp2 eq_refl).
  - right.
    destruct (canonical p w) as [A T].
    destruct T as [B T].
    subst.
    exists A.
    constructor.
  - right.
    destruct s as [e' T].
    exists (π1 e').
    constructor.
    all: auto.
  - right.
    destruct (canonical p w) as [A T].
    destruct T as [B T].
    subst.
    exists B.
    constructor.
  - right.
    destruct s as [e' T].
    exists (π2 e').
    constructor.
    all: auto.
  - right.
    destruct (canonical p1 w) as [x T].
    destruct T as [body T].
    subst.
    exists ([x := e1] body).
    constructor.
  - right.
    destruct (canonical p1 w) as [x T].
    destruct T as [body T].
    subst.
    exists ([x := e1] body).
    constructor.
  - right.
    destruct s as [e0' T].
    exists (app e0' e1).
    constructor.
    all: auto.
  - right.
    destruct s as [e0' T].
    exists (app e0' e1).
    constructor.
    all: auto.
  - right.
    destruct (canonical p w) as [e0 T].
    subst.
    exists e0.
    constructor.
  - right.
    destruct s as [e' T].
    exists (ext κ e').
    constructor.
    all: auto.
  - right.
    destruct (canonical p w) as [e0 T].
    subst.
    exists (necessity κ (necessity κ e0)).
    constructor.
  - right.
    destruct s as [e' T].
    exists (dup e').
    constructor.
    auto.
  - right.
    destruct (canonical p1 w) as [e0' T].
    subst.
    exists ([x := e0'] e1).
    constructor.
  - right.
    destruct s as [e' T].
    exists (bind e' x e1).
    constructor.
    auto.
  - right.
    destruct (canonical p2 w0).
    subst.
    destruct (canonical p1 w).
    subst.
    exists (id κ2).
    constructor.
  - right.
    destruct s as [e' T].
    exists (e0 ∘ e').
    constructor.
    auto.
  - right.
    destruct s as [e' T].
    exists (e' ∘ e1).
    constructor.
    auto.
  - right.
    destruct s as [e' T].
    exists (e' ∘ e1).
    constructor.
    auto.
  - right.
    destruct (canonical p w).
    subst.
    exists (id κ0).
    constructor.
  - right.
    destruct s as [e' T].
    exists (sym e').
    constructor.
    auto.
  - right.
    destruct (canonical p1 w).
    subst.
    destruct (canonical p2 w0) as [e' T].
    subst.
    exists (box κ1 e').
    constructor.
  - right.
    destruct s as [e' T].
    exists (cast_pos e0 e').
    constructor.
    auto.
  - right.
    destruct s as [e' T].
    exists (cast_pos e' e1).
    constructor.
    auto.
  - right.
    destruct s as [e' T].
    exists (cast_pos e' e1).
    constructor.
    auto.
  - right.
    destruct (canonical p1 w).
    destruct (canonical p2 w0) as [e' T].
    subst.
    exists (necessity κ1 e').
    constructor.
  - right.
    destruct s as [e' T].
    exists (cast_nec e0 e').
    constructor.
    auto.
  - right.
    destruct s as [e' T].
    exists (cast_nec e' e1).
    constructor.
    auto.
  - right.
    destruct s as [e' T].
    exists (cast_nec e' e1).
    constructor.
    auto.
Defined.

Theorem preservation (e e': tm) τ:
    e ~> e' →
    mt ⊢ e ∈ τ →
    mt ⊢ e' ∈ τ.
Proof.
  remember mt as Γ.
  intros st.
  generalize dependent τ.
  induction st.
  all: subst.
  all: intros τ0 p.
  all: inversion p.
  all: subst.
  - inversion H1.
    subst.
    apply (subst_type H0 H3).
  - inversion H3.
    subst.
    apply (subst_type H4 H0).
  - inversion H0.
    subst.
    auto.
  - inversion H0.
    subst.
    auto.
  - inversion H2.
    subst.
    auto.
  - inversion H0.
    subst.
    apply judge_necessity.
    apply judge_necessity.
    auto.
  - inversion H0.
    subst.
    auto.
  - inversion H1.
    subst.
    auto.
  - inversion H1.
    subst.
    auto.
  - inversion H1.
    subst.
    auto.
  - eapply judge_bind.
    Unshelve.
    3: apply τ1.
    2: auto.
    apply IHst.
    auto.
  - eapply judge_app.
    Unshelve.
    3: apply τ1.
    all: auto.
  - eapply judge_π1.
    Unshelve.
    2: apply τ2.
    all: auto.
  - eapply judge_π2.
    Unshelve.
    2: apply τ1.
    all: auto.
  - constructor.
    auto.
  - constructor.
    auto.
  - eapply judge_compose.
    Unshelve.
    3: apply κ1.
    all: auto.
  - eapply judge_compose.
    Unshelve.
    3: apply κ1.
    all: auto.
  - constructor.
    auto.
  - eapply judge_cast_pos.
    Unshelve.
    3: apply κ0.
    all: auto.
  - eapply judge_cast_pos.
    Unshelve.
    3: apply κ0.
    all: auto.
  - eapply judge_cast_nec.
    Unshelve.
    3: apply κ0.
    all: auto.
  - eapply judge_cast_nec.
    Unshelve.
    3: apply κ0.
    all: auto.
Defined.

Inductive multistep (X: tm): tm → Type :=
| halt: multistep X X
| andthen {Y Z}: X ~> Y → multistep Y Z → multistep X Z.
Arguments halt {X}.
Arguments andthen {X Y Z}.

Notation "A ~>* B" := (multistep A B) (at level 90).

Fixpoint eval (e: tm): option tm :=
  match e with
  | app (lam x _ e0) e1 => Some ([x := e1] e0)
  | bind (box _ e0) x e1 => Some ([x := e0] e1)

  | π1 (fanout e0 _) => Some e0
  | π2 (fanout _ e1) => Some e1

  | ext _ (necessity _ e) => Some e
  | dup (necessity κ e) => Some (necessity κ (necessity κ e))

  | sym (id κ) => Some (id κ)
  | id κ ∘ id _ => Some (id κ)

  | cast_pos (id κ) (box _ e) => Some (box κ e)
  | cast_nec (id κ) (necessity _ e) => Some (necessity κ e)

  | app e0 e1 =>
    eval e0 >>= λ e0',
    Some (app e0' e1)

  | π1 e =>
    eval e >>= λ e',
    Some (π1 e')
  | π2 e =>
    eval e >>= λ e',
    Some (π2 e')

  | ext κ e =>
    eval e >>= λ e',
    Some (ext κ e')

  | dup e =>
    eval e >>= λ e',
    Some (dup e')

  | e0 ∘ e1 =>
    if eval e0 is Some e0'
    then Some (e0' ∘ e1)
    else
      if eval e1 is Some e1'
      then Some (e0 ∘ e1')
      else None

  | cast_pos e0 e1 =>
    if eval e0 is Some e0'
    then Some (cast_pos e0' e1)
    else
      if eval e1 is Some e1'
      then Some (cast_pos e0 e1')
      else None

  | cast_nec e0 e1 =>
    if eval e0 is Some e0'
    then Some (cast_nec e0' e1)
    else
      if eval e1 is Some e1'
      then Some (cast_nec e0 e1')
      else None

  | _ => None
  end.
