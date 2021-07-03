Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Import IfNotations.
Import ListNotations.

Close Scope nat.

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

Inductive tm {v α} :=
| var (x: v)

| lam (x: v) (s: sort α) (e: tm)
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
| bind (e0: tm) (x: v) (e1: tm)

| id (κ: α)
| compose (e0 e1: tm)
| sym (e: tm)

| cast_pos (e0 e1: tm)
| cast_nec (e0 e1: tm)
.

Arguments tm: clear implicits.

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

Record prop A :=
  impl {
      head: A ;
      tail: list A ;
    }.
Arguments impl {A}.
Arguments head {A}.
Arguments tail {A}.

Notation "{ P ———— Q }" := (impl Q P).

Variant judgement :=
| judge_var_head
| judge_var_tail

| judge_tt

| judge_fanout
| judge_fst
| judge_snd

| judge_lam
| judge_app

| judge_necessity

| judge_nec_comm

| judge_ext
| judge_dup

| judge_pos_comm

| judge_box
| judge_bind

| judge_id
| judge_compose
| judge_sym

| judge_cast_nec
| judge_cast_pos
.

Definition judge v α (r: judgement): bundle (prop (ofty v α)) :=
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
  | judge_nec_comm =>
    sup '(Γ, κ0, κ1, τ, e), {
      [Γ ⊢ e ∈ (□ κ1, □ κ0, τ)]
      ————
      Γ ⊢ nec_comm e ∈ (□ κ1, □ κ0, τ)
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

  | judge_pos_comm =>
    sup '(Γ, κ0, κ1, τ, e), {
      [Γ ⊢ e ∈ (◇ κ0, ◇ κ1, τ)]
      ————
      Γ ⊢ pos_comm e ∈ (◇ κ1, ◇ κ0, τ)
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

  (* Really unsure of these as faithful to cylindrical logic *)
  | judge_cast_pos =>
    sup '(Γ, κ0, κ1, τ, e0, e1), {
      [Γ ⊢ e0 ∈ (κ0 ~ κ1) ;
       Γ ⊢ e1 ∈ (◇ κ0, τ) ]
      ————
      Γ ⊢ cast_pos e0 e1 ∈ (◇ κ1, τ)
    }
  | judge_cast_nec =>
    sup '(Γ, κ0, κ1, τ, e0, e1), {
      [Γ ⊢ e0 ∈ (κ0 ~ κ1) ;
       Γ ⊢ e1 ∈ (□ κ0, τ) ]
      ————
      Γ ⊢ cast_nec e0 e1 ∈ (□ κ1, τ)
    }
  end.

Inductive proof v α: list (ofty v α) → Type :=
| QED: proof v α []
| andso
    {T}
    (r: judgement)
    (s: judge v α r)
  :
    proof v α (tail (π (judge v α r) s) ++ T) →
    proof v α (head (π (judge v α r) s) :: T).

Arguments QED {v α}.
Arguments andso {v α T}.

Notation "A # B ; C" := (andso A B C) (at level 60, right associativity,
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

Record heap v α := { top: nat ; read: nat → tm v α ;}.
Arguments top {v α}.
Arguments read {v α}.

Definition alloc {v α} (σ: heap v α) (e: tm v α): nat * heap v α :=
  let ix := top σ in
  (ix, {| top := S ix ; read n := if Nat.eqb n ix then e else read σ n |}).

Record big v α := big_intro {
  env: list (v * nat) ;
  from: heap v α * tm v α;
  to: heap v α * tm v α;
}.
Arguments big_intro {v α}.
Arguments env {v α}.
Arguments from {v α}.
Arguments to {v α}.

Notation "s ⊨ A ⇓ B" := (big_intro s A B) (at level 80).

Variant label :=
| label_var_head
| label_var_tail

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

Definition reduce v α (l: label): bundle (prop (big v α)) :=
  match l with
(* FIXME environment/store is probably all wrong :( *)
  | label_var_head =>
    sup '(Γ, σ, x, n), {
      []
      ————
      (x, n) :: Γ ⊨ (σ, var x) ⇓ (σ, read σ n)
    }
  | label_var_tail =>
    sup '(Γ, H, x, σ, e), {
      [Γ ⊨ (σ, var x) ⇓ (σ, e)]
      ————
      H :: Γ ⊨ (σ, var x) ⇓ (σ, e)
    }

  | label_tt =>
    sup '(Γ, σ), {
      []
      ————
      Γ ⊨ (σ, tt) ⇓ (σ, tt)
    }
  | label_id =>
    sup '(Γ, σ, κ), {
      []
      ————
      Γ ⊨ (σ, id κ) ⇓ (σ, id κ)
    }
  | label_fanout =>
    sup '(Γ, σ, e0, e1), {
      []
      ————
      Γ ⊨ (σ, ⟨ e0, e1 ⟩) ⇓ (σ, ⟨ e0 , e1 ⟩)
    }
  | label_lam =>
    sup '(Γ, σ, x, τ, e), {
      []
      ————
      Γ ⊨ (σ, lam x τ e) ⇓ (σ, lam x τ e)
    }
  | label_necessity =>
    sup '(Γ, σ, κ, e), {
      []
      ————
      Γ ⊨ (σ, necessity κ e) ⇓ (σ, necessity κ e)
    }
  | label_box =>
    sup '(Γ, σ, κ, e), {
      []
      ————
      Γ ⊨ (σ, box κ e) ⇓ (σ, box κ e)
    }

  | label_ext_necessity =>
    sup '(Γ, σ0, σ1, κ, e0, e1), {
      [Γ ⊨ (σ0, e0) ⇓ (σ1, necessity κ e1)]
      ————
      Γ ⊨ (σ0, ext κ e0) ⇓ (σ1, e1)
    }
  | label_dup =>
    sup '(Γ, σ0, σ1, κ, e0, e1), {
      [Γ ⊨ (σ0, e0) ⇓ (σ1, necessity κ e1)]
      ————
      Γ ⊨ (σ0, dup e0) ⇓ (σ1, necessity κ (necessity κ e1))
    }

  | label_app =>
    sup '(Γ, σ0, σ1, σ2, x, τ, e0, e1, e2, e3), {
      [Γ ⊨ (σ0, e0) ⇓ (σ1, lam x τ e2) ;
      (
        let '(ix, σ1') := alloc σ1 e1 in
        (x, ix) :: Γ ⊨ (σ1', e2) ⇓ (σ2, e3)
      )
      ]
      ————
      Γ ⊨ (σ0, app e0 e1) ⇓ (σ2, e3)
    }

  | label_bind =>
    sup '(Γ, σ0, σ1, σ2, x, κ, e0, e1, e2, e3), {
      [Γ ⊨ (σ0, e0) ⇓ (σ1, box κ e2) ;
      (
        let '(ix, σ1') := alloc σ1 e2 in
        (x, ix) :: Γ ⊨ (σ1', e1) ⇓ (σ2, e3)
      )
      ]
      ————
      Γ ⊨ (σ0, bind e0 x e1) ⇓ (σ2, e3)
    }

  | label_π1_fanout =>
    sup '(Γ, σ0, σ1, e0, e1, e2), {
      [Γ ⊨ (σ0, e0) ⇓ (σ1, ⟨e1, e2⟩) ]
      ————
      Γ ⊨ (σ0, π1 e0) ⇓ (σ1, e1)
    }
  | label_π2_fanout =>
    sup '(Γ, σ0, σ1, e0, e1, e2), {
      [Γ ⊨ (σ0, e0) ⇓ (σ1, ⟨e1, e2⟩) ]
      ————
      Γ ⊨ (σ0, π2 e0) ⇓ (σ1, e2)
    }

  | label_nec_comm =>
     sup '(Γ, σ0, σ1, κ0, κ1, e0, e1), {
      [Γ ⊨ (σ0, e0) ⇓ (σ1, necessity κ0 (necessity κ1 e1))]
      ————
      Γ ⊨ (σ0, nec_comm e0) ⇓ (σ1, necessity κ1 (necessity κ0 e1))
    }
  | label_pos_comm =>
     sup '(Γ, σ0, σ1, κ0, κ1, e0, e1), {
      [Γ ⊨ (σ0, e0) ⇓ (σ1, box κ0 (box κ1 e1))]
      ————
      Γ ⊨ (σ0, pos_comm e0) ⇓ (σ1, box κ1 (box κ0 e1))
    }


  | label_compose_id =>
    sup '(Γ, σ0, σ1, σ2, κ, e0, e1), {
      [Γ ⊨ (σ0, e0) ⇓ (σ1, id κ); Γ ⊨ (σ1, e1) ⇓ (σ2, id κ)]
      ————
      Γ ⊨ (σ0, e0 ∘ e1) ⇓ (σ2, id κ)
    }

  | label_sym_id =>
    sup '(Γ, σ0, σ1, κ, e), {
      [Γ ⊨ (σ0, e) ⇓ (σ1, id κ)]
      ————
      Γ ⊨ (σ0, sym e) ⇓ (σ1, id κ)
    }

  | label_cast_pos =>
    sup '(Γ, σ0, σ1, σ2, κ, e0, e1, e2), {
      [Γ ⊨ (σ0, e0) ⇓ (σ1, id κ) ;
       Γ ⊨ (σ1, e1) ⇓ (σ2, box κ e2)
      ]
      ————
      Γ ⊨ (σ0, cast_nec e0 e1) ⇓ (σ2, e2)
    }

  | label_cast_nec =>
    sup '(Γ, σ0, σ1, σ2, κ, e0, e1, e2), {
      [Γ ⊨ (σ0, e0) ⇓ (σ1, id κ) ;
       Γ ⊨ (σ1, e1) ⇓ (σ2, necessity κ e2)
      ]
      ————
      Γ ⊨ (σ0, cast_nec e0 e1) ⇓ (σ2, e2)
    }
  end
.
(* Unfortunately seq cannot be the same as proof due to weird
inference issues *)

Inductive seq v α: list (big v α) → Type :=
| HALT: seq v α []
| step
    {T}
    (r: label)
    (s: reduce v α r)
  :
    seq v α (tail (π (reduce v α r) s) ++ T) →
    seq v α (head (π (reduce v α r) s) :: T).

Arguments HALT {v α}.
Arguments step {v α T}.

Notation "A @ B ; C" := (step A B C) (at level 60, right associativity,
                                      format "A  @  B  ; '//' C").

Example seq_id v α κ σ: seq v α [[] ⊨ (σ, id κ ∘ id κ) ⇓ (σ, id κ)] :=
  label_compose_id @ ([], σ,σ,σ, κ, id κ, id κ) ;
  label_id @ ([], σ, κ) ;
  label_id @ ([], σ, κ) ;
  HALT.

Example seq_sym v α κ σ: seq v α [[] ⊨ (σ, sym (id κ)) ⇓ (σ, id κ)]
  :=
  label_sym_id @ ([], σ, σ, κ, id κ) ;
  label_id @ ([], σ, κ) ;
  HALT.
