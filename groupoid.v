#[global]
Set Primitive Projections.
#[global]
Unset Printing Primitive Projection Parameters.

#[global]
Set Universe Polymorphism.

#[global]
Set Default Goal Selector "!".

Require Import Coq.Unicode.Utf8.
Require Import Coq.Strings.String.

Inductive term :=
| undef
| type
| set
| all (x: string) (e0 e1: term)

| var (x: string)
| lam (x: string) (e0 e1: term)
| app (e0 e1: term)

| cast (p e0: term)
| trans (e0 e1: term)
| sym (e: term)
| beta (x: string) (A e0 e1: term)
| K (e0 e1: term)
.
Definition subst x e: term → term :=
  fix loop (t: term) :=
    match t with
    | undef => undef

    | type => type
    | set => set
    | all y A e => if string_dec x y then all y (loop A) e else all y (loop A) (loop e)

    | var y => if string_dec x y then e else t
    | lam y A e => if string_dec x y then lam y (loop A) e else lam y (loop A) (loop e)
    | app e0 e1 => app (loop e0) (loop e1)

    | cast p e => cast (loop p) (loop e)
    | trans e0 e1 => trans (loop e0) (loop e1)
    | sym e => sym (loop e)
    | K e e' => K (loop e) (loop e')
    | beta y A f e => if string_dec x y then beta y (loop A) f (loop e) else beta y (loop A) (loop f) (loop e)
  end.

Definition mt (_: string): term := undef.
Definition put x A (Γ: string → term) : string → term :=
  λ y, if string_dec x y then A else Γ y.

Reserved Notation "Γ ⊢ x ∈ A" (at level 80).
Reserved Notation "Γ ⊢ x ; A ≡ B" (at level 80).

Inductive
  types (Γ: string → term): term → term → Type :=
| types_var x: Γ ⊢ var x ∈ Γ x
| types_set: Γ ⊢ set ∈ type

| types_all K L x A B:
    Γ ⊢ A ∈ K →
    put x A Γ ⊢ B ∈ L →
    Γ ⊢ all x A B ∈ L

| types_lam K x A B e:
    Γ ⊢ A ∈ K →
    put x A Γ ⊢ e ∈ B →
    Γ ⊢ lam x A e ∈ all x A B

| types_app x e0 e1 A B:
    Γ ⊢ e0 ∈ all x A B →
    Γ ⊢ e1 ∈ A →
    Γ ⊢ app e0 e1 ∈ subst x e1 B

| types_trans A e0 e1:
    Γ ⊢ e0 ∈ A →
    Γ ⊢ e1 ∈ A →
    Γ ⊢ trans e0 e1 ∈ A
| types_sym A e:
    Γ ⊢ e ∈ A →
    Γ ⊢ sym e ∈ A
| types_beta x A B e0 e1:
    Γ ⊢ app (lam x A e0) e1 ∈ B →
    Γ ⊢ subst x e1 e0 ∈ B →
    Γ ⊢ beta x A e0 e1 ∈ B
| types_K e e' A:
    Γ ⊢ e ∈ A →
    Γ ⊢ e' ∈ A →
    Γ ⊢ K e e' ∈ A

| types_cast K p q e0 e1 :
    Γ ⊢ e0 ∈ K →
    Γ ⊢ e0 ; p ≡ q →
    Γ ⊢ e1 ∈ p →
    Γ ⊢ cast e0 e1 ∈ q
where "Γ ⊢ x ∈ A" := (types Γ x A)
with
  coerces (Γ: string → term): term → term → term → Type :=
  (* FIXME alpha conversion ? *)
  (* also seems sus *)
| coerces_var x: Γ ⊢ var x ; var x ≡ var x

| coerces_set: Γ ⊢ set ; set ≡ set
| coerces_lam x A e p p' q q':
    Γ ⊢ A ; p ≡ p' →
    put x A Γ ⊢ e ; q ≡ q' →
    Γ ⊢ lam x A e ; lam x p q ≡ lam x p' q'
| coerces_app e0 e1 p p' q q':
    Γ ⊢ e0 ; p ≡ p' →
    Γ ⊢ e1 ; q ≡ q' →
    Γ ⊢ app e0 e1 ; app p q ≡ app p' q'

| coerces_cast p q r s e0 e1 :
    Γ ⊢ e0 ; p ≡ q →
    Γ ⊢ e1 ; r ≡ s →
    Γ ⊢ cast e0 e1 ; r ≡ s

| coerces_trans e0 e1 p q r:
    Γ ⊢ e0 ; p ≡ q →
    Γ ⊢ e1 ; q ≡ r →
    Γ ⊢ trans e0 e1 ; p ≡ r
| coerces_sym e p q:
    Γ ⊢ e ; p ≡ q →
    Γ ⊢ sym e ; q ≡ p
(* IDK here at all, weird *)
| coerces_K e e' p q:
    Γ ⊢ e ; p ≡ q →
    Γ ⊢ e' ; p ≡ q →
    Γ ⊢ K e e' ; e ≡ e'
| coerces_beta x A e0 e1:
    Γ ⊢ beta x A e0 e1 ; app (lam x A e0) e1 ≡ subst x e1 e0
where "Γ ⊢ x ; P ≡ Q" := (coerces Γ x P Q).
