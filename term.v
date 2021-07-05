Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector.
Require Import Coq.Bool.Bool.
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
Add Printing Let someT.

Arguments some_intro [A P].
Arguments head [A P].
Arguments tail [A P].

Module Import SomeNotations.
  Notation "'some' x .. y , P" := (someT (λ x, .. (someT (λ y,  P)) .. )) : type_scope.
  Notation "'Σ' x .. y , P" := (someT (λ x, .. (someT (λ y,  P)) .. )) : type_scope.
  Notation "⟨ x , y , .. , z ⟩" := (some_intro .. (some_intro x y) .. z) : core_scope.
End SomeNotations.

 Inductive sort {α} :=
| unit
| prod (A B: sort)
| exp (s t: sort)
| pos (κ: α) (A: sort)
| nec (κ: α) (A: sort)
| eq (κ μ: α).

Arguments sort: clear implicits.

Notation "[ A , B ]" := (exp A B).
Infix "×" := prod (at level 50).

Notation "◇ κ , A" := (pos κ A) (at level 200).
Notation "□ κ , A" := (nec κ A) (at level 200).
Infix "~" := eq (at level 90).

Reserved Notation "f ∘ g" (at level 30).

(* Strings are really dumb but I don't want to figure out two things
at the same time *)

Inductive tm {α}: Type :=
| var (x: string)

| lam (x: string) (s: sort α) (e: tm)
| app (f x: tm)

| tt

| fanout (e0 e1: tm)
| π1 (e: tm)
| π2 (e: tm)

| necessity (κ: α) (e: tm)
| nec_comm (e: tm)

| ext (κ: α) (e: tm)
| dup (e: tm)

| pos_comm (e: tm)
| box (κ: α) (e: tm)
| bind (e0: tm) (x: string) (e1: tm)

| id (κ: α)
| compose (e0 e1: tm)
| sym (e: tm)

| cast_pos (e0 e1: tm)
| cast_nec (e0 e1: tm)
.

Arguments tm: clear implicits.

Infix "∘" := compose.

Definition ctx α := string → option (sort α).
Definition mt {α}: ctx α := λ _, None.
Definition add {α} x τ (m: ctx α): ctx α := λ y, if string_dec x y then Some τ else m y.

Reserved Notation "Γ ⊢ e ∈ τ" (at level 80).

Inductive judge {α} (Γ: ctx α): tm α → sort α → Type :=
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
| judge_nec_comm κ0 κ1 e τ:
    Γ ⊢ e ∈ (□ κ0, □ κ1, τ) →
    Γ ⊢ nec_comm e ∈ (□ κ1, □ κ0, τ)

| judge_ext κ e τ:
    Γ ⊢ e ∈ (□ κ, τ) →
    Γ ⊢ ext κ e ∈ τ
| judge_dup κ e τ:
    Γ ⊢ e ∈ (□ κ, τ) →
    Γ ⊢ dup e ∈ (□ κ, □ κ, τ)

| judge_pos_comm κ0 κ1 e τ:
    Γ ⊢ e ∈ (◇ κ0, ◇ κ1, τ) →
    Γ ⊢ pos_comm e ∈ (◇ κ1, ◇ κ0, τ)

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

Section infer.
  Context {α: Type} (eq_dec: forall (κ0 κ1: α), {κ0 = κ1} + {κ0 ≠ κ1}).

  Definition sort_eq (x y: sort α): {x = y} + {x ≠ y}.
  Proof.
    decide equality.
  Defined.

  Fixpoint infer (Γ: ctx α) (e: tm α): option (sort α) :=
    match e with
    | var x => Γ x

    | lam x τ0 e =>
      match infer (add x τ0 Γ) e with
      | Some τ1 => Some [τ0, τ1]
      | _ => None
      end

    | app e0 e1 =>
      match (infer Γ e0, infer Γ e1) with
      | (Some [τ0, τ1], Some τ0') =>
        if sort_eq τ0 τ0' then
          Some τ1
        else
          None
      | _ => None
      end

    | tt => Some unit

    | fanout e0 e1 =>
      match (infer Γ e0, infer Γ e1) with
      | (Some τ0, Some τ1) => Some (τ0 × τ1)
      | _ => None
      end

    | π1 e =>
      match infer Γ e with
      | Some (τ0 × τ1) => Some τ0
      | _ => None
      end

    | π2 e =>
      match infer Γ e with
      | Some (τ0 × τ1) => Some τ1
      | _ => None
      end

    | necessity κ e =>
      match infer mt e with
      | Some τ => Some (□ κ, τ)
      | _ => None
      end
    | nec_comm e =>
      match infer Γ e with
      | Some (□ κ0, □ κ1, τ) => Some (□ κ1, □ κ0, τ)
      | _ => None
      end

    | ext κ e =>
      match infer Γ e with
      | Some (□ κ', τ) =>
        if eq_dec κ κ' then Some τ else None
      | _ => None
      end
    | dup e =>
      match infer Γ e with
      | Some (□ κ, τ) => Some (□ κ, □ κ, τ)
      | _ => None
      end

    | pos_comm e =>
      match infer Γ e with
      | Some (◇ κ0, ◇ κ1, τ) => Some (◇ κ1, ◇ κ0, τ)
      | _ => None
      end

    | box κ e =>
      match infer Γ e with
      | Some τ => Some (◇ κ, τ)
      | _ => None
      end

    | bind e0 x e1 =>
      match infer Γ e0 with
      | Some (◇ κ0, τ0) =>
        match infer (add x τ0 Γ) e1 with
        | Some (◇ κ1, τ1) =>
          if eq_dec κ0 κ1 then Some (◇ κ1, τ1) else None
        | _ => None
        end
      | _ => None
      end

    | id κ => Some (κ ~ κ)
    | e0 ∘ e1 =>
      match (infer Γ e0, infer Γ e1) with
      | (Some (κ1 ~ κ2), Some (κ0 ~ κ1')) =>
        if eq_dec κ1 κ1' then Some (κ0 ~ κ2) else None
      | _ => None
      end

    | sym e =>
      match infer Γ e with
      | Some (κ0 ~ κ1) => Some (κ1 ~ κ0)
      | _ => None
      end


    | cast_pos e0 e1 =>
      match (infer Γ e0, infer Γ e1) with
      | (Some (κ0 ~ κ1), Some (◇ κ0', τ)) =>
        if eq_dec κ0 κ0' then Some (◇ κ1, τ) else None
      | _ => None
      end

    | cast_nec e0 e1 =>
      match (infer Γ e0, infer Γ e1) with
      | (Some (κ0 ~ κ1), Some (□ κ0', τ)) =>
        if eq_dec κ0 κ0' then Some (□ κ1, τ) else None
      | _ => None
      end
    end.

  Theorem infer_sound Γ e τ:
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
      2: discriminate.
      destruct s.
      all: try discriminate.
      destruct (infer Γ e2) eqn:q2.
      all: try discriminate.
      destruct (sort_eq s1 s).
      all: try discriminate.
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
      destruct s.
      all: try discriminate.
      destruct s.
      all: try discriminate.
      inversion p.
      subst.
      apply judge_nec_comm.
      apply IHe.
      assumption.
    - destruct (infer Γ e) eqn:q.
      all: try discriminate.
      destruct s.
      all: try discriminate.
      destruct (eq_dec κ κ0).
      all: try discriminate.
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
      destruct s.
      all: try discriminate.
      destruct s.
      all: try discriminate.
      inversion p.
      subst.
      apply judge_pos_comm.
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
      destruct s.
      all: try discriminate.
      destruct (infer (add x s Γ) e2) eqn:q2.
      all: try discriminate.
      destruct s0.
      all: try discriminate.
      destruct (eq_dec κ κ0).
      all: try discriminate.
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
      destruct s.
      all: try discriminate.
      destruct (infer Γ e2) eqn:q2.
      all: try discriminate.
      destruct s.
      all: try discriminate.
      destruct (eq_dec κ μ0).
      all: try discriminate.
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
      destruct s.
      all: try discriminate.
      inversion p.
      subst.
      apply judge_sym.
      apply IHe.
      assumption.
    - destruct (infer Γ e1) eqn:q1.
      all: try discriminate.
      destruct s.
      all: try discriminate.
      destruct (infer Γ e2) eqn:q2.
      all: try discriminate.
      destruct s.
      all: try discriminate.
      destruct (eq_dec κ κ0).
      all: try discriminate.
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
      destruct s.
      all: try discriminate.
      destruct (infer Γ e2) eqn:q2.
      all: try discriminate.
      destruct s.
      all: try discriminate.
      destruct (eq_dec κ κ0).
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

  Theorem infer_complete Γ e τ :
    Γ ⊢ e ∈ τ → infer Γ e = Some τ.
    intro p.
    induction p.
    all: cbn in *.
    all: auto.
    - rewrite IHp1, IHp2.
      reflexivity.
    - rewrite IHp.
      reflexivity.
    - rewrite IHp.
      reflexivity.
    - rewrite IHp.
      reflexivity.
    - rewrite IHp1, IHp2.
      destruct (sort_eq τ0 τ0).
      2: contradiction.
      reflexivity.
    - rewrite IHp.
      reflexivity.
    - rewrite IHp.
      reflexivity.
    - rewrite IHp.
      destruct (eq_dec κ κ).
      2: contradiction.
      reflexivity.
    - rewrite IHp.
      destruct (eq_dec κ κ).
      2: contradiction.
      reflexivity.
    - rewrite IHp.
      reflexivity.
    - rewrite IHp.
      reflexivity.
    - rewrite IHp1, IHp2.
      destruct (eq_dec κ κ).
      2: contradiction.
      reflexivity.
    - rewrite IHp1, IHp2.
      destruct (eq_dec κ1 κ1).
      2: contradiction.
      reflexivity.
    - rewrite IHp.
      reflexivity.
    - rewrite IHp1, IHp2.
      destruct (eq_dec κ0 κ0).
      2: contradiction.
      reflexivity.
    - rewrite IHp1, IHp2.
      destruct (eq_dec κ0 κ0).
      2: contradiction.
      reflexivity.
  Qed.
End infer.

Variant whnf {α}: tm α → Type :=
| whnf_tt: whnf tt
| whnf_fanout e0 e1: whnf (fanout e0 e1)
| whnf_lam x τ e: whnf (lam x τ e)
| whnf_box κ e: whnf (box κ e)
| whnf_nec κ e: whnf (necessity κ e)
| whnf_id κ: whnf (id κ)
.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst {α} (x : string) (s : tm α) (ev : tm α) : tm α :=
  match ev with
  | var y =>
    if string_dec x y
    then s
    else ev

  | lam y τ e =>
    if string_dec x y
    then ev
    else lam y τ ([x := s] e)
  | bind e0 y e1 =>
    bind ([x := s] e0) y (if string_dec x y then e1 else [x := s] e1)

  | tt => tt

  | app e0 e1 => app ([x:=s] e0) ([x:=s] e1)

  | fanout e0 e1 => fanout ([x:=s] e0) ([x:=s] e1)
  | π1 e => π1 ([x:=s] e)
  | π2 e => π2 ([x:=s] e)

  | necessity κ e => necessity κ ([x:=s] e)
  | nec_comm e => nec_comm ([x:=s] e)

  | ext κ e => ext κ ([x:=s] e)
  | dup e => dup ([x:=s] e)

  | pos_comm e => pos_comm ([x:=s] e)
  | box κ e => box κ ([x:=s] e)

  | id κ => id κ
  | e0 ∘ e1 => ([x:=s] e0) ∘ ([x:=s] e1)
  | sym e => sym ([x:=s] e)

  | cast_pos e0 e1 => cast_pos ([x:=s] e0) ([x:=s] e1)
  | cast_nec e0 e1 => cast_nec ([x:=s] e0) ([x:=s] e1)
  end
where "'[' x ':=' s ']' t" := (subst x s t) .

Theorem subst_type {α} Γ x τ2 (e0 e1: tm α) τ0 τ1:
  add x τ2 Γ ⊢ e0 ∈ τ0 →
  mt ⊢ e1 ∈ τ1 →
  Γ ⊢ [x:=e1]e0 ∈ τ0.
Proof.
  intros p q.
  generalize dependent Γ.
  generalize dependent τ0.
  induction e0.
  all: intros.
  all: cbn in *.
  - destruct (string_dec x x0).
    + subst.
Admitted.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step {α} : tm α → tm α → Prop :=
  | step_app_lam x τ e0 e1:
      app (lam x τ e0) e1 --> [x:=e1]e0
  | step_bind_box κ e0 x e1:
      bind (box κ e0) x e1 --> [x:=e0]e1

  | step_π1_fanout e0 e1:
      π1 (fanout e0 e1) --> e0
  | step_π2_fanout e0 e1:
      π2 (fanout e0 e1) --> e1

  | step_ext_necessity κ e:
      ext κ (necessity κ e) --> e
  | step_dup_necessity κ e:
      ext κ (necessity κ e) --> necessity κ (necessity κ e)

  | step_sym_id κ:
      sym (id κ) --> id κ
  | step_compose_id κ:
      id κ ∘ id κ --> id κ

  | step_cast_pos_id_box κ e:
      cast_pos (id κ) (box κ e) --> box κ e
  | step_cast_nec_id_box κ e:
      cast_nec (id κ) (necessity κ e) --> necessity κ e

  | step_app e0 e0' e1:
      e0 --> e0' →
      app e0 e1 --> app e0' e1
  | step_π1 e e':
      e --> e' →
      π1 e --> π1 e'
  | step_π2 e e':
      e --> e' →
      π2 e --> π2 e'

  | step_ext κ e e':
      e --> e' →
      ext κ e --> ext κ e'
  | step_dup e e':
      e --> e' →
      dup e --> dup e'

  | step_pos_comm e e':
      e --> e' →
      pos_comm e --> pos_comm e'

  | step_nec_comm e e':
      e --> e' →
      nec_comm e --> nec_comm e'

  | step_compose_l e0 e0' e1:
      e0 --> e0' →
      e0 ∘ e1 --> e0' ∘ e1
  | step_compose_r e0 e1 e1':
      e1 --> e1' →
      e0 ∘ e1 --> e0 ∘ e1'

  | step_cast_pos_l e0 e1 e0':
      e0 --> e0' →
      cast_pos e0 e1 --> cast_pos e0' e1
  | step_cast_pos_r e0 e1 e1':
      e1 --> e1' →
      cast_pos e0 e1 --> cast_pos e0 e1'


  | step_cast_nec_l e0 e1 e0':
      e0 --> e0' →
      cast_nec e0 e1 --> cast_nec e0' e1
  | step_cast_nec_r e0 e1 e1':
      e1 --> e1' →
      cast_nec e0 e1 --> cast_nec e0 e1'

where "t '-->' t'" := (step t t').
