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

Theorem add_add {α} x τ0 τ1 (m: ctx α): add x τ0 (add x τ1 m) = add x τ0 m.
Proof.
  extensionality y.
  unfold add.
  destruct (string_dec x y).
  all: reflexivity.
Qed.

Theorem add_comm {α} x y τ0 τ1 (m: ctx α):
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

  Theorem infer_complete {Γ e τ}:
    Γ ⊢ e ∈ τ → infer Γ e = Some τ.
    intro p.
    induction p.
    all: cbn in *.
    all: auto.
    all: try rewrite IHp.
    all: try rewrite IHp1.
    all: try rewrite IHp2.
    all: try reflexivity.
    - destruct (sort_eq τ0 τ0).
      2: contradiction.
      reflexivity.
    - destruct (eq_dec κ κ).
      2: contradiction.
      reflexivity.
    - destruct (eq_dec κ κ).
      2: contradiction.
      reflexivity.
    - destruct (eq_dec κ1 κ1).
      2: contradiction.
      reflexivity.
    - destruct (eq_dec κ0 κ0).
      2: contradiction.
      reflexivity.
    - destruct (eq_dec κ0 κ0).
      2: contradiction.
      reflexivity.
  Qed.
End infer.

Definition includes {α} (Γ Δ: ctx α): Prop :=
  ∀ x τ, Δ x = Some τ → Γ x = Some τ.

Notation "Γ ⊑ Δ" := (includes Γ Δ) (at level 90).

Instance include_refl α: Reflexive (@includes α).
Proof.
  intros ? ? ? ?.
  auto.
Qed.

Instance include_trans α: Transitive (@includes α).
Proof.
  intros ? ? ? p q ? ? ?.
  unfold includes in p, q.
  apply p.
  apply q.
  auto.
Qed.

Theorem weaken {α Γ Δ} {e: tm α} {τ}:
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

Variant whnf {α}: tm α → Type :=
| whnf_tt: whnf tt
| whnf_fanout e0 e1: whnf (fanout e0 e1)
| whnf_lam x τ e: whnf (lam x τ e)
| whnf_box κ e: whnf (box κ e)
| whnf_nec κ e: whnf (necessity κ e)
| whnf_id κ: whnf (id κ)
.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Section subst.
  Context {α: Type} (x: string) (s: tm α).
  Fixpoint subst (ev: tm α): tm α :=
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
    | nec_comm e => nec_comm (subst e)

    | ext κ e => ext κ (subst e)
    | dup e => dup (subst e)

    | pos_comm e => pos_comm (subst e)
    | box κ e => box κ (subst e)

    | id κ => id κ
    | e0 ∘ e1 =>  (subst e0) ∘ (subst e1)
    | sym e => sym (subst e)

    | cast_pos e0 e1 => cast_pos (subst e0) (subst e1)
    | cast_nec e0 e1 => cast_nec (subst e0) (subst e1)
    end.
End subst.

Notation "'[' x ':=' s ']' t" := (subst x s t) .

Theorem subst_type {α} {Γ x} {e0 e1: tm α} {τ0 τ1}
   (eq_dec: forall (κ0 κ1: α), {κ0 = κ1} + {κ0 ≠ κ1}):
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
      set (p' := infer_complete eq_dec p).
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
      set (p' := infer_complete eq_dec p).
      unfold add in p'.
      cbn in *.
      rewrite r in p'.
      apply judge_var.
      auto.
  - cbn in *.
    destruct (string_dec x x0).
    + subst.
      apply judge_lam.
      rewrite add_add in X.
      assumption.
    + apply judge_lam.
      apply IHe0.
      rewrite add_comm.
      1: assumption.
      assumption.
  - cbn.
    apply IHe0.
    refine (weaken _ X).
    intros ? ? ?.
    unfold mt in *.
    discriminate.
  - cbn.
    destruct (string_dec x x0).
    + subst.
      rewrite add_add in X0.
      auto.
    + apply IHe0_2.
      rewrite add_comm in X0.
      2: auto.
      auto.
Qed.

Reserved Notation "t '~>' t'" (at level 40).

Inductive step {α}: tm α → tm α → Type :=
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

| step_app e0 e0' e1:
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

| step_pos_comm e e':
    e ~> e' →
    pos_comm e ~> pos_comm e'

| step_nec_comm e e':
    e ~> e' →
    nec_comm e ~> nec_comm e'

| step_compose_l e0 e0' e1:
    e0 ~> e0' →
    e0 ∘ e1 ~> e0' ∘ e1
| step_compose_r e0 e1 e1':
    e1 ~> e1' →
    e0 ∘ e1 ~> e0 ∘ e1'

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

Inductive multistep {α} (X: tm α): tm α → Type :=
| halt: multistep X X
| andthen {Y Z}: X ~> Y → multistep Y Z → multistep X Z.
Arguments halt {α X}.
Arguments andthen {α X Y Z}.

Notation "A ~>* B" := (multistep A B) (at level 90).

Fixpoint eval {α} (e: tm α): option (tm α) :=
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
    if eval e0 is Some e0'
    then Some (app e0' e1)
    else None

  | π1 e =>
    if eval e is Some e'
    then Some (π1 e')
    else None
  | π2 e =>
    if eval e is Some e'
    then Some (π2 e')
    else None

  | ext κ e =>
    if eval e is Some e'
    then Some (ext κ e')
    else None

  | dup e =>
    if eval e is Some e'
    then Some (dup e')
    else None

  | e0 ∘ e1 =>
    if eval e0 is Some e0'
    then Some (e0' ∘ e1)
    else
      if eval e1 is Some e1'
      then Some (e0 ∘ e1')
      else None

  | pos_comm e =>
    if eval e is Some e'
    then Some (pos_comm e')
    else None

  | nec_comm e =>
    if eval e is Some e'
    then Some (nec_comm e')
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

CoInductive stream A := cons { hd: A ; tl: option (stream A) }.

Arguments cons {A}.
Arguments hd {A}.
Arguments tl {A}.

CoFixpoint multieval {α} (e: tm α): stream (tm α) :=
  cons e (if eval e is Some e' then Some (multieval e') else None).

Inductive evalsto {α} (X: tm α): tm α → Type :=
| evals_id: evalsto X X
| evals_step {Y Z}: Some Y = eval X → evalsto Y Z → evalsto X Z.
Arguments evals_id {α X}.
Arguments evals_step {α X Y Z}.
