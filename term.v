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

Inductive tm v :=
| var (x: v)

| lam (x: v) (s: sort) (e: tm v)
| app (f x: tm v)

| tt

| fanout (e0 e1: tm v)
| π1 (e: tm v)
| π2 (e: tm v)

| necessity (κ: α) (e: tm v)
| ext (κ: α) (e: tm v)
| dup (e: tm v)

| box (κ: α) (e: tm v)
| bind (e0: tm v) (x: v) (e1: tm v)

| id (κ: α)
| compose (e0 e1: tm v)
| sym (e: tm v)
.

Arguments var {v}.

Arguments lam {v}.
Arguments app {v}.

Arguments tt {v}.

Arguments fanout {v}.
Arguments π1 {v}.
Arguments π2 {v}.

Arguments necessity {v}.
Arguments ext {v}.
Arguments dup {v}.

Arguments box {v}.
Arguments bind {v}.

Arguments id {v}.
Arguments compose {v}.
Arguments sym {v}.

Infix "∘" := compose.
Notation "⟨ x , y , .. , z ⟩" := (fanout .. (fanout x y) .. z).

Record ofty v := ofty_intro {
  Γ: list (v * sort) ;
  e: tm v ;
  τ: sort ;
}.
Arguments ofty_intro {v}.
Arguments Γ {v}.
Arguments e {v}.
Arguments τ {v}.
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
| judge_var_head
| judge_var_tail

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

Definition judge v (r: rule): bundle (prop (ofty v)) :=
  match r with
  | judge_var_head =>
    sup '(Γ, τ, x), {
      []
      ————
      (x, τ) :: Γ ⊢ var x ∈ τ
    }
  | judge_var_tail =>
    (* Not sure how to deal with variable shadowing  *)
    sup '(Γ, H, τ, x), {
      [(x, τ) :: Γ ⊢ var x ∈ τ]
      ————
      H :: Γ ⊢ var x ∈ τ
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
    sup '(Γ, τ0, τ1, x, e), {
      [(x, τ0) :: Γ ⊢ e ∈ τ1]
      ————
      Γ ⊢ lam x τ0 e ∈ [τ0, τ1]
    }
  | judge_app =>
    sup '(Γ, τ0, τ1, e0, e1), {
      [Γ ⊢ e0 ∈ τ0]
      ————
      Γ ⊢ app e0 e1 ∈ τ1
    }

  | judge_necessity =>
    sup '(Γ, κ, τ, e), {
      [[] ⊢ e ∈ τ]
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
    sup '(Γ, κ, τ0, τ1, x, e0, e1), {
      [Γ ⊢ e0 ∈ (□ κ, τ0) ;
       ((x, τ0) :: Γ) ⊢ e1 ∈ (□ κ, τ1)]
      ————
      Γ ⊢ bind e0 x e1 ∈ (□ κ, τ1)
    }

(* FIXME add commutativity rules *)
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

Inductive proof v: list (ofty v) → Type :=
| QED: proof v []
| step
    {T}
    (r: rule)
    (s: judge v r)
  :
    proof v (tail (π (judge v r) s) ++ T) →
    proof v (head (π (judge v r) s) :: T).

Arguments QED {v}.
Arguments step {v T}.

Notation "A # B ; C" := (step A B C) (at level 60, right associativity,
                                      format "A  #  B  ; '//' C").

Example proof_tt v: proof v [[] ⊢ tt ∈ unit] :=
  judge_tt # _ ;
  QED.

Example proof_compose v κ: proof v [[] ⊢ id κ ∘ id κ ∈ (κ ~ κ)]
  :=
    judge_compose # ([], κ, κ, κ, id κ, id κ) ;
    judge_id # ([], κ) ;
    judge_id # ([], κ) ;
    QED.

Example proof_id v x A: proof v [[] ⊢ lam x A (var x) ∈ [A, A]]
  :=
  judge_lam # ([], A, A, x, var x) ;
  judge_var_head # ([], A, x) ;
  QED.

Example proof_const v x y A B: proof v [[] ⊢ lam x A (lam y B (var x)) ∈ [A, [B, A]]]
:=
judge_lam # ([], A, [B, A], x, lam y B (var x)) ;
judge_lam # ([(x, A)], B, A, y, var x) ;
judge_var_tail # ([(x, A)], (y, B), A, x) ;
judge_var_head # ([(x, A)], A, x) ;
QED.
