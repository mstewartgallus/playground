Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Import IfNotations.
Import ListNotations.

Close Scope nat.

Inductive sort α :=
| unit
| prod (A B: sort α)
| exp (s t: sort α)
| pos (κ: α) (A: sort α)
| nec (κ: α) (A: sort α)
| eq (κ μ: α).

Arguments unit {α}.
Arguments prod {α}.
Arguments exp {α}.
Arguments pos {α}.
Arguments nec {α}.
Arguments eq {α}.

Notation "[ A , B ]" := (exp A B).
Infix "×" := prod (at level 50).

Notation "◇ κ , A" := (pos κ A) (at level 200).
Notation "□ κ , A" := (nec κ A) (at level 200).
Infix "~" := eq (at level 90).

Reserved Notation "f ∘ g" (at level 30).

Inductive tm v α :=
| var (x: v)

| lam (x: v) (s: sort α) (e: tm v α)
| app (f x: tm v α)

| tt

| fanout (e0 e1: tm v α)
| π1 (e: tm v α)
| π2 (e: tm v α)

| necessity (κ: α) (e: tm v α)
| ext (κ: α) (e: tm v α)
| dup (e: tm v α)

| box (κ: α) (e: tm v α)
| bind (e0: tm v α) (x: v) (e1: tm v α)

| id (κ: α)
| compose (e0 e1: tm v α)
| sym (e: tm v α)
.

Arguments var {v α}.

Arguments lam {v α}.
Arguments app {v α}.

Arguments tt {v α}.

Arguments fanout {v α}.
Arguments π1 {v α}.
Arguments π2 {v α}.

Arguments necessity {v α}.
Arguments ext {v α}.
Arguments dup {v α}.

Arguments box {v α}.
Arguments bind {v α}.

Arguments id {v α}.
Arguments compose {v α}.
Arguments sym {v α}.

Infix "∘" := compose.
Notation "⟨ x , y , .. , z ⟩" := (fanout .. (fanout x y) .. z).

Record ofty v α := ofty_intro {
  Γ: list (v * sort α) ;
  e: tm v α;
  τ: sort α;
}.
Arguments ofty_intro {v α}.
Arguments Γ {v α}.
Arguments e {v α}.
Arguments τ {v α}.
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

Definition judge v α (r: rule): bundle (prop (ofty v α)) :=
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

(* Inductive forest v := *)
(* | mt *)
(* | premise: list (ofty v) → forest v → forest v. *)

Inductive proof v α: list (ofty v α) → Type :=
| QED: proof v α []
| step
    {T}
    (r: rule)
    (s: judge v α r)
  :
    proof v α (tail (π (judge v α r) s) ++ T) →
    proof v α (head (π (judge v α r) s) :: T).

Arguments QED {v α}.
Arguments step {v α T}.

Notation "A # B ; C" := (step A B C) (at level 60, right associativity,
                                      format "A  #  B  ; '//' C").

Example proof_tt v α: proof v α [[] ⊢ tt ∈ unit] :=
  judge_tt # _ ;
  QED.

Example proof_compose v α κ: proof v α [[] ⊢ id κ ∘ id κ ∈ (κ ~ κ)]
  :=
    judge_compose # ([], κ, κ, κ, id κ, id κ) ;
    judge_id # ([], κ) ;
    judge_id # ([], κ) ;
    QED.

Example proof_id v α x A: proof v α [[] ⊢ lam x A (var x) ∈ [A, A]]
  :=
  judge_lam # ([], A, A, x, var x) ;
  judge_var_head # ([], A, x) ;
  QED.

Example proof_const v α x y A B: proof v α [[] ⊢ lam x A (lam y B (var x)) ∈ [A, [B, A]]] :=
  judge_lam # ([], A, [B, A], x, lam y B (var x)) ;
  judge_lam # ([(x, A)], B, A, y, var x) ;
  judge_var_tail # ([(x, A)], (y, B), A, x) ;
  judge_var_head # ([(x, A)], A, x) ;
  QED.

Example proof_nec_tt v α κ: proof v α [[] ⊢ necessity κ tt ∈ □ κ, unit] :=
  judge_necessity # ([], κ, unit, tt) ;
  judge_tt # [] ;
  QED.
