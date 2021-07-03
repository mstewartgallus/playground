Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Import IfNotations.
Import ListNotations.

Close Scope nat.

Definition α := nat.
Inductive sort :=
| unit
| prod (A B: sort)
| exp (s t: sort)
| pos (κ:α) (A: sort)
| nec (κ:α) (A: sort)
| eq (κ μ: α).

Notation "[ A , B ]" := (exp A B).
Infix "×" := prod (at level 50).

Notation "◇ κ , A" := (pos κ A) (at level 200).
Notation "□ κ , A" := (nec κ A) (at level 200).
Infix "~" := eq (at level 90).

Reserved Notation "f ∘ g" (at level 30).

Inductive tm :=
| var (n: nat)

| lam (s: sort) (e: tm)
| app (f x: tm)

| tt

| fanout (e0 e1: tm)
| π1 (e: tm)
| π2 (e: tm)

| necessity (κ: α) (e: tm)
| ext (κ: α) (e: tm)
| dup (e: tm)

| box (κ: α) (e: tm)
| bind (e0 e1: tm)

| id (κ: α)
| compose (e0 e1: tm)
| sym (e: tm)
.
Infix "∘" := compose.
Notation "⟨ x , y , .. , z ⟩" := (fanout .. (fanout x y) .. z).

CoInductive stream A := cons { hd: A ; tl: stream A; }.
Arguments cons {A}.
Arguments hd {A}.
Arguments tl {A}.
Infix "&" := cons (at level 50).

Fixpoint ff {A} n (s: stream A) :=
  match n with
  | O => s
  | S n' => ff n' (tl s)
  end.

CoFixpoint mt: stream sort := cons unit mt.
Notation "∅" := mt.

Record ofty := ofty_intro {
  Γ: stream sort ;
  e: tm ;
  τ: sort ;
}.
Notation "Γ ⊢ e ∈ τ" := (ofty_intro Γ e τ) (at level 80).

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


Reserved Notation "{ P ———— Q }" (at level 90, format "{ '//' P '//' ———— '//' Q }").

Record prop A := impl {
                     head: A ;
                     tail: list A ;
                     }.

Arguments impl {A}.
Arguments head {A}.
Arguments tail {A}.

Notation "{ P ———— Q }" := (impl Q P).

Variant rule :=
| judge_var

| judge_tt

| judge_fanout
| judge_fst
| judge_snd

| judge_lam
| judge_app

| judge_necessity
| judge_ext
| judge_dup

| judge_box
| judge_bind

| judge_id
| judge_compose
| judge_sym
.

Definition judge (r: rule): bundle (prop ofty) :=
  match r with
  | judge_var =>
    sup '(Γ, n), {
      []
      ————
      Γ ⊢ var n ∈ hd (ff n Γ)
    }

  | judge_tt =>
    sup Γ, {
      []
      ————
      Γ ⊢ tt ∈ unit
    }
  | judge_fanout =>
    sup '(Γ, τ0, τ1, e0, e1), {
      [ Γ ⊢ e0 ∈ τ0 ; Γ ⊢ e1 ∈ τ1]
      ————
      Γ ⊢ ⟨ e0, e1 ⟩ ∈ (τ0 × τ1)
    }
  | judge_fst =>
    sup '(Γ, τ0, τ1, e), {
      [Γ ⊢ e ∈ (τ0 × τ1) ]
      ————
      Γ ⊢ π1 e ∈ τ0
    }
  | judge_snd =>
    sup '(Γ, τ0, τ1, e0, e1), {
      [ Γ ⊢ e0 ∈ τ0 ]
      ————
      Γ ⊢ ⟨ e0, e1 ⟩ ∈ (τ0 × τ1)
    }

  | judge_lam =>
    sup '(Γ, τ0, τ1, e), {
      [τ0 & Γ ⊢ e ∈ τ1]
      ————
      Γ ⊢ lam τ0 e ∈ [τ0, τ1]
    }
  | judge_app =>
    sup '(Γ, τ0, τ1, e0, e1), {
      [Γ ⊢ e0 ∈ τ0]
      ————
      Γ ⊢ app e0 e1 ∈ τ1
    }

  | judge_necessity =>
    sup '(Γ, κ, τ, e), {
      [∅ ⊢ e ∈ τ]
      ————
      Γ ⊢ necessity κ e ∈ (□ κ, τ)
    }
  | judge_ext =>
    sup '(Γ, κ, τ, e), {
      [Γ ⊢ e ∈ (□ κ, τ)]
      ————
      Γ ⊢ ext κ e ∈ τ
    }
  | judge_dup =>
    sup '(Γ, κ, τ, e), {
      [Γ ⊢ e ∈ (□ κ, τ)]
      ————
      Γ ⊢ dup e ∈ (□ κ, □ κ, τ)
    }

  | judge_box =>
    sup '(Γ, κ, τ, e), {
      [Γ ⊢ e ∈ τ]
      ————
      Γ ⊢ box κ e ∈ (□ κ, τ)
    }
  | judge_bind =>
    sup '(Γ, κ, τ0, τ1, e0, e1), {
      [Γ ⊢ e0 ∈ (□ κ, τ0) ;
       (τ0 & Γ) ⊢ e1 ∈ (□ κ, τ1)]
      ————
      Γ ⊢ bind e0 e1 ∈ (□ κ, τ1)
    }

  | judge_id =>
    sup '(Γ, κ), {
      []
      ————
      Γ ⊢ id κ ∈ (κ ~ κ)
    }
  | judge_compose =>
    sup '(Γ, κ0, κ1, κ2, e0, e1), {
      [Γ ⊢ e0 ∈ (κ1 ~ κ2) ; Γ ⊢ e0 ∈ (κ0 ~ κ1) ]
      ————
      Γ ⊢ (e0 ∘ e1) ∈ (κ0 ~ κ2)
    }
  | judge_sym =>
    sup '(Γ, e, κ0, κ1), {
      [Γ ⊢ e ∈ (κ0 ~ κ1) ]
      ————
      Γ ⊢ sym e ∈ (κ1 ~ κ0)
    }
  end.

Inductive proof: list ofty → Type :=
| QED: proof []
| step
    (r: rule)
    (s: judge r)
    {T}
  :
    proof (tail (π (judge r) s) ++ T) →
    proof (head (π (judge r) s) :: T).

Notation "A # B >> C" := (step A B C) (at level 60, right associativity).
Definition proof_tt: proof [mt ⊢ tt ∈ unit] :=
  judge_tt # _ >>
  QED.

Definition proof_compose κ: proof [mt ⊢ id κ ∘ id κ ∈ (κ ~ κ)]
  :=
    judge_compose # (∅, κ, κ, κ, id κ, id κ) >>
    judge_id # (∅, κ) >>
    judge_id # (∅, κ) >>
    QED.
