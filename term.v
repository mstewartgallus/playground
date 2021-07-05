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

Inductive judge {α}: ctx α → tm α → sort α → Type :=
| judge_var Γ x τ:
    Γ x = Some τ →
    Γ ⊢ var x ∈ τ

| judge_tt Γ:
    Γ ⊢ tt ∈ unit
| judge_fanout Γ e0 e1 τ0 τ1:
    Γ ⊢ e0 ∈ τ0 → Γ ⊢ e1 ∈ τ1 →
    Γ ⊢ fanout e0 e1 ∈ (τ0 × τ1)

| judge_π1 Γ e τ0 τ1:
    Γ ⊢ e ∈ (τ0 × τ1) →
    Γ ⊢ π1 e ∈ τ0
| judge_π2 Γ e τ0 τ1:
    Γ ⊢ e ∈ (τ0 × τ1) →
    Γ ⊢ π2 e ∈ τ1

| judge_lam Γ e τ0 τ1 x:
    add x τ0 Γ ⊢ e ∈ τ1 →
    Γ ⊢ lam x τ0 e ∈ [τ0, τ1]
| judge_app Γ e0 e1 τ0 τ1:
    Γ ⊢ e0 ∈ [τ0, τ1] → Γ ⊢ e1 ∈ τ0 →
    Γ ⊢ app e0 e1 ∈ τ1

| judge_necessity Γ κ e τ:
    mt ⊢ e ∈ τ →
    Γ ⊢ necessity κ e ∈ (□ κ, τ)
| judge_nec_comm Γ κ0 κ1 e τ:
    Γ ⊢ e ∈ (□ κ0, □ κ1, τ) →
    Γ ⊢ nec_comm e ∈ (□ κ1, □ κ0, τ)

| judge_ext Γ κ e τ:
    Γ ⊢ e ∈ (□ κ, τ) →
    Γ ⊢ ext κ e ∈ τ
| judge_dup Γ κ e τ:
    Γ ⊢ e ∈ (□ κ, τ) →
    Γ ⊢ dup e ∈ (□ κ, □ κ, τ)

| judge_pos_comm Γ κ0 κ1 e τ:
    Γ ⊢ e ∈ (◇ κ0, ◇ κ1, τ) →
    Γ ⊢ pos_comm e ∈ (◇ κ1, ◇ κ0, τ)

| judge_box Γ κ e τ:
    Γ ⊢ e ∈ τ →
    Γ ⊢ box κ e ∈ (◇ κ, τ)

| judge_bind Γ e0 e1 x κ τ0 τ1:
    Γ ⊢ e0 ∈ (◇ κ, τ0) → add x τ0 Γ ⊢ e1 ∈ (◇ κ, τ1) →
    Γ ⊢ bind e0 x e1 ∈ (◇ κ, τ1)

| judge_id Γ κ:
    Γ ⊢ id κ ∈ (κ ~ κ)

| judge_compose Γ e0 e1 κ0 κ1 κ2:
    Γ ⊢ e0 ∈ (κ1 ~ κ2) → Γ ⊢ e1 ∈ (κ0 ~ κ1) →
    Γ ⊢ (e0 ∘ e1) ∈ (κ0 ~ κ2)

| judge_sym Γ e κ0 κ1:
    Γ ⊢ e ∈ (κ1 ~ κ0) →
    Γ ⊢ sym e ∈ (κ0 ~ κ1)

(* Really unsure of these as faithful to cylindrical logic *)
| judge_cast_pos Γ e0 e1 κ0 κ1 τ:
      Γ ⊢ e0 ∈ (κ0 ~ κ1) → Γ ⊢ e1 ∈ (◇ κ0, τ) →
      Γ ⊢ cast_pos e0 e1 ∈ (◇ κ1, τ)
| judge_cast_nec Γ e0 e1 κ0 κ1 τ:
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

Record heap α := { top: nat ; read: nat → tm α ;}.
Arguments top {α}.
Arguments read {α}.

Definition alloc {α} (σ: heap α) (e: tm α): nat * heap α :=
  let ix := top σ in
  (ix, {| top := S ix ; read n := if Nat.eqb n ix then e else read σ n |}).
(* FIXME just do the damn substitution *)

Record big α := big_intro {
  env: F.t nat ;
  from: heap α * tm α;
  to: heap α * tm α;
}.
Arguments big_intro {α}.
Arguments env {α}.
Arguments from {α}.
Arguments to {α}.

Notation "s ⊨ A ⇓ B" := (big_intro s A B) (at level 80).

Variant label :=
| label_var

| label_tt
| label_fanout
| label_lam
| label_necessity
| label_box
| label_id

| label_app
| label_bind

| label_π1_fanout
| label_π2_fanout

| label_nec_comm
| label_pos_comm

| label_dup
| label_ext_necessity

| label_compose_id
| label_sym_id

| label_cast_pos
| label_cast_nec
.

(* pretty hacky *)
Definition load (x: string) (Γ: F.t nat): nat :=
  if F.find x Γ is Some n then n else O.

Record bundle A := sup {
  s: Type ;
  π: s → A ;
}.
Arguments sup {A}.
Arguments π {A}.

Coercion s: bundle >-> Sortclass.

Notation "'sup' x .. y , P" := {| π x := .. {| π y := P |} .. |}
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' 'sup'  x .. y ']' , '/' P ']'").


Reserved Notation "P ———— Q" (at level 90, format "'//' P '//' ———— '//' Q").

Record prop A :=
  impl {
      consequent: A ;
      antecedent: list A ;
    }.
Arguments impl {A}.
Arguments consequent {A}.
Arguments antecedent {A}.

Notation "P ———— Q" := (impl Q P).


Definition reduce α (l: label): bundle (prop (big α)) :=
  match l with
(* FIXME environment/store is probably all wrong :( *)
  | label_var =>
    sup '(Γ, σ, x), (
      []
      ————
      Γ ⊨ (σ, var x) ⇓ (σ, read σ (load x Γ))
    )
  | label_tt =>
    sup '(Γ, σ), (
      []
      ————
      Γ ⊨ (σ, tt) ⇓ (σ, tt)
    )
  | label_id =>
    sup '(Γ, σ, κ), (
      []
      ————
      Γ ⊨ (σ, id κ) ⇓ (σ, id κ)
    )
  | label_fanout =>
    sup '(Γ, σ, e0, e1), (
      []
      ————
      Γ ⊨ (σ, fanout e0 e1) ⇓ (σ, fanout e0 e1)
    )
  | label_lam =>
    sup '(Γ, σ, x, τ, e), (
      []
      ————
      Γ ⊨ (σ, lam x τ e) ⇓ (σ, lam x τ e)
    )
  | label_necessity =>
    sup '(Γ, σ, κ, e), (
      []
      ————
      Γ ⊨ (σ, necessity κ e) ⇓ (σ, necessity κ e)
    )
  | label_box =>
    sup '(Γ, σ, κ, e), (
      []
      ————
      Γ ⊨ (σ, box κ e) ⇓ (σ, box κ e)
    )

  | label_ext_necessity =>
    sup '(Γ, σ0, σ1, κ, e0, e1), (
      [Γ ⊨ (σ0, e0) ⇓ (σ1, necessity κ e1)]
      ————
      Γ ⊨ (σ0, ext κ e0) ⇓ (σ1, e1)
    )
  | label_dup =>
    sup '(Γ, σ0, σ1, κ, e0, e1), (
      [Γ ⊨ (σ0, e0) ⇓ (σ1, necessity κ e1)]
      ————
      Γ ⊨ (σ0, dup e0) ⇓ (σ1, necessity κ (necessity κ e1))
    )

  | label_app =>
    sup '(Γ, σ0, σ1, σ2, x, τ, e0, e1, e2, e3), (
      [Γ ⊨ (σ0, e0) ⇓ (σ1, lam x τ e2) ;
      (
        let '(ix, σ1') := alloc σ1 e1 in
        F.add x ix Γ ⊨ (σ1', e2) ⇓ (σ2, e3)
      )
      ]
      ————
      Γ ⊨ (σ0, app e0 e1) ⇓ (σ2, e3)
    )

  | label_bind =>
    sup '(Γ, σ0, σ1, σ2, x, κ, e0, e1, e2, e3), (
      [Γ ⊨ (σ0, e0) ⇓ (σ1, box κ e2) ;
      (
        let '(ix, σ1') := alloc σ1 e2 in
        F.add x ix Γ ⊨ (σ1', e1) ⇓ (σ2, e3)
      )
      ]
      ————
      Γ ⊨ (σ0, bind e0 x e1) ⇓ (σ2, e3)
    )

  | label_π1_fanout =>
    sup '(Γ, σ0, σ1, e0, e1, e2), (
      [Γ ⊨ (σ0, e0) ⇓ (σ1, fanout e1 e2) ]
      ————
      Γ ⊨ (σ0, π1 e0) ⇓ (σ1, e1)
    )
  | label_π2_fanout =>
    sup '(Γ, σ0, σ1, e0, e1, e2), (
      [Γ ⊨ (σ0, e0) ⇓ (σ1, fanout e1 e2) ]
      ————
      Γ ⊨ (σ0, π2 e0) ⇓ (σ1, e2)
    )

  | label_nec_comm =>
     sup '(Γ, σ0, σ1, κ0, κ1, e0, e1), (
      [Γ ⊨ (σ0, e0) ⇓ (σ1, necessity κ0 (necessity κ1 e1))]
      ————
      Γ ⊨ (σ0, nec_comm e0) ⇓ (σ1, necessity κ1 (necessity κ0 e1))
    )
  | label_pos_comm =>
     sup '(Γ, σ0, σ1, κ0, κ1, e0, e1), (
      [Γ ⊨ (σ0, e0) ⇓ (σ1, box κ0 (box κ1 e1))]
      ————
      Γ ⊨ (σ0, pos_comm e0) ⇓ (σ1, box κ1 (box κ0 e1))
    )


  | label_compose_id =>
    sup '(Γ, σ0, σ1, σ2, κ, e0, e1), (
      [Γ ⊨ (σ0, e0) ⇓ (σ1, id κ); Γ ⊨ (σ1, e1) ⇓ (σ2, id κ)]
      ————
      Γ ⊨ (σ0, e0 ∘ e1) ⇓ (σ2, id κ)
    )

  | label_sym_id =>
    sup '(Γ, σ0, σ1, κ, e), (
      [Γ ⊨ (σ0, e) ⇓ (σ1, id κ)]
      ————
      Γ ⊨ (σ0, sym e) ⇓ (σ1, id κ)
    )

  | label_cast_pos =>
    sup '(Γ, σ0, σ1, σ2, κ, e0, e1, e2), (
      [Γ ⊨ (σ0, e0) ⇓ (σ1, id κ) ;
       Γ ⊨ (σ1, e1) ⇓ (σ2, box κ e2)
      ]
      ————
      Γ ⊨ (σ0, cast_nec e0 e1) ⇓ (σ2, e2)
    )

  | label_cast_nec =>
    sup '(Γ, σ0, σ1, σ2, κ, e0, e1, e2), (
      [Γ ⊨ (σ0, e0) ⇓ (σ1, id κ) ;
       Γ ⊨ (σ1, e1) ⇓ (σ2, necessity κ e2)
      ]
      ————
      Γ ⊨ (σ0, cast_nec e0 e1) ⇓ (σ2, e2)
    )
  end
.
(* Unfortunately seq cannot be the same as proof due to weird
inference issues *)

Inductive seq α: list (big α) → Type :=
| HALT: seq α []
| step
    {T}
    (r: label)
    (s: reduce α r)
  :
    seq α (antecedent (π (reduce α r) s) ++ T) →
    seq α (consequent (π (reduce α r) s) :: T).

Arguments HALT {α}.
Arguments step {α T} r s &.

Notation "A @ B ; C" := (step A B C) (at level 60, right associativity,
                                      format "A  @  B  ; '//' C").

Example seq_id α κ σ: seq α [F.empty _ ⊨ (σ, id κ ∘ id κ) ⇓ (σ, id κ)] :=
  label_compose_id @ (F.empty _, σ,σ,σ, κ, id κ, id κ) ;
  label_id @ (F.empty _, σ, κ) ;
  label_id @ (F.empty _, σ, κ) ;
  HALT.

Example seq_sym α κ σ: seq α [F.empty _ ⊨ (σ, sym (id κ)) ⇓ (σ, id κ)]
  :=
  label_sym_id @ (F.empty _, σ, σ, κ, id κ) ;
  label_id @ (F.empty _, σ, κ) ;
  HALT.
