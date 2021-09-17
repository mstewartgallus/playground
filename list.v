
#[global]
Set Primitive Projections.
#[global]
Unset Printing Primitive Projection Parameters.

#[global]
Set Universe Polymorphism.

#[global]
Set Default Goal Selector "!".

Require Import Coq.Unicode.Utf8.
Require Import Coq.Program.Tactics.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Psatz.

Import IfNotations.
Import ListNotations.

Definition Π y: list Type → Type :=
  fix loop l :=
    match l with
    | [] => unit
    | H :: T => prod (y H) (loop T)
    end.

Definition Mor (A B: list Type) :=
   ∀ x, Π (λ a, x → a) A → Π (λ b, x → b) B.

Definition map {A B} (f: A → B): Mor [A] [B].
Proof.
  intros ? [H ?].
  apply (λ x, f (H x), tt).
Defined.

Definition fst: ∀ {A B}, Mor (A ++ B) A.
Proof.
  intros A B.
  intros ? X.
  induction A.
  all: cbn in *.
  - apply tt.
  - destruct X as [H T].
    split.
    + apply H.
    + apply IHA.
      apply T.
Defined.

Definition snd: ∀ {A B}, Mor (A ++ B) B.
Proof.
  intros A.
  induction A.
  - intros ? ? X.
    cbn.
    apply X.
  - intros ? ? [H T].
    cbn in *.
    apply IHA.
    auto.
Defined.

Definition fanout:
  ∀ A B C,
  Mor C A → Mor C B → Mor C (A ++ B).
Proof.
  intro A.
  induction A.
  all: cbn in *.
  - intros ? ? ? g.
    apply g.
  - intros ? ? f g ? X.
    cbn.
    split.
    + apply f.
      cbn in *.
      auto.
    + refine (IHA _ _ _ g _ _).
      * intros ? ?.
        apply f.
        cbn.
        auto.
      * apply X.
Defined.

Definition entail A B := ∀ x, Π (λ a, x → a) A → (x → B).
Infix "⊢" := entail (at level 90).

Definition index: ∀ {A} (Γ: list A) n, (n < length Γ) → A.
Proof.
  intros ? Γ n.
  induction n.
  - intros p.
    destruct Γ as [|H T].
    1: cbn in *; Psatz.lia.
    apply H.
  - intro.
    apply IHn.
    Psatz.lia.
Defined.

Definition var {Γ} n p: Γ ⊢ index Γ n p.
Proof.
  induction n.
  - destruct Γ.
    1: cbn in *;Psatz.lia.
    intros ? [H ?] ?.
    apply H.
    auto.
  - intros ? H x.
    apply (IHn _ _ H x).
Defined.

Definition curry {A B Γ} (f: (A :: Γ) ⊢ B): Γ ⊢ (A → B).
Proof.
  intros T X t a.
  apply (f T (λ _, a, X) t).
Defined.

#[program]
Definition foo {Γ A}: A :: Γ ⊢ A := var 0 _.

Next Obligation.
Proof.
  Psatz.lia.
Qed.
