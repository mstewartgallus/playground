Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import IfNotations.
Import ListNotations.
Open Scope string_scope.

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
Notation "⟨ x , y , .. , z ⟩" := (fanout .. (fanout x y) .. z).

Definition ns (A: Type): nat → Type :=
  fix loop n :=
    match n with
    | O => True
    | S n' => A * loop n'
    end.
Record ctx α := map {
  σ: list string ;
  ty: ns (sort α) (List.length σ);
}.
Arguments map {α}.
Arguments σ {α}.
Arguments ty {α}.
Definition mt {α}: ctx α := map [] I.
Notation "A |-> B" := (map A B) (at level 30).
Record ofty α := ofty_intro {
  Γ: ctx α ;
  e: tm α;
  τ: sort α;
}.
Arguments ofty_intro {α}.
Arguments Γ {α}.
Arguments e {α}.
Arguments τ {α}.
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


Reserved Notation "P ———— Q" (at level 90, format "'//' P '//' ———— '//' Q").

Record prop A :=
  impl {
      head: A ;
      tail: list A ;
    }.
Arguments impl {A}.
Arguments head {A}.
Arguments tail {A}.

Notation "P ———— Q" := (impl Q P).

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

Definition judge α (r: judgement): bundle (prop (ofty α)) :=
  match r with
  | judge_var_head =>
    sup '(Γ, x, τ), (
      []
      ————
      (x :: σ Γ) |-> (τ, ty Γ) ⊢ var x ∈ τ
    )

  | judge_var_tail =>
    sup '(y, H, Γ, x, τ), (
      [Γ ⊢ var x ∈ τ]
      ————
      (y :: σ Γ) |-> (H, ty Γ) ⊢ var x ∈ τ
    )

  | judge_tt =>
    sup Γ, (
      []
      ————
      Γ ⊢ tt ∈ unit
    )
  | judge_fanout =>
    sup '(Γ, τ0, τ1, e0, e1), (
      [ Γ ⊢ e0 ∈ τ0 ; Γ ⊢ e1 ∈ τ1]
      ————
      Γ ⊢ ⟨ e0, e1 ⟩ ∈ (τ0 × τ1)
    )
  | judge_fst =>
    sup '(Γ, τ0, τ1, e), (
      [Γ ⊢ e ∈ (τ0 × τ1) ]
      ————
      Γ ⊢ π1 e ∈ τ0
    )
  | judge_snd =>
    sup '(Γ, τ0, τ1, e0, e1), (
      [ Γ ⊢ e0 ∈ τ0 ]
      ————
      Γ ⊢ ⟨ e0, e1 ⟩ ∈ (τ0 × τ1)
    )

  | judge_lam =>
    sup '(Γ, τ0, τ1, x, e), (
      [map (x :: σ Γ) (τ0, ty Γ) ⊢ e ∈ τ1]
      ————
      Γ ⊢ lam x τ0 e ∈ [τ0, τ1]
    )
  | judge_app =>
    sup '(Γ, τ0, τ1, e0, e1), (
      [Γ ⊢ e0 ∈ τ0]
      ————
      Γ ⊢ app e0 e1 ∈ τ1
    )

  | judge_necessity =>
    sup '(Γ, κ, τ, e), (
      [mt ⊢ e ∈ τ]
      ————
      Γ ⊢ necessity κ e ∈ (□ κ, τ)
    )
  | judge_nec_comm =>
    sup '(Γ, κ0, κ1, τ, e), (
      [Γ ⊢ e ∈ (□ κ1, □ κ0, τ)]
      ————
      Γ ⊢ nec_comm e ∈ (□ κ1, □ κ0, τ)
    )

  | judge_ext =>
    sup '(Γ, κ, τ, e), (
      [Γ ⊢ e ∈ (□ κ, τ)]
      ————
      Γ ⊢ ext κ e ∈ τ
    )
  | judge_dup =>
    sup '(Γ, κ, τ, e), (
      [Γ ⊢ e ∈ (□ κ, τ)]
      ————
      Γ ⊢ dup e ∈ (□ κ, □ κ, τ)
    )

  | judge_pos_comm =>
    sup '(Γ, κ0, κ1, τ, e), (
      [Γ ⊢ e ∈ (◇ κ0, ◇ κ1, τ)]
      ————
      Γ ⊢ pos_comm e ∈ (◇ κ1, ◇ κ0, τ)
    )

  | judge_box =>
    sup '(Γ, κ, τ, e), (
      [Γ ⊢ e ∈ τ]
      ————
      Γ ⊢ box κ e ∈ (□ κ, τ)
    )
  | judge_bind =>
    sup '(Γ, κ, τ0, τ1, x, e0, e1), (
      [Γ ⊢ e0 ∈ (□ κ, τ0) ;
      (x :: σ Γ) |-> (τ0, ty Γ) ⊢ e1 ∈ (□ κ, τ1)]
      ————
      Γ ⊢ bind e0 x e1 ∈ (□ κ, τ1)
    )

  | judge_id =>
    sup '(Γ, κ), (
      []
      ————
      Γ ⊢ id κ ∈ (κ ~ κ)
    )
  | judge_compose =>
    sup '(Γ, κ0, κ1, κ2, e0, e1), (
      [Γ ⊢ e0 ∈ (κ1 ~ κ2) ; Γ ⊢ e0 ∈ (κ0 ~ κ1) ]
      ————
      Γ ⊢ (e0 ∘ e1) ∈ (κ0 ~ κ2)
    )
  | judge_sym =>
    sup '(Γ, e, κ0, κ1), (
      [Γ ⊢ e ∈ (κ0 ~ κ1) ]
      ————
      Γ ⊢ sym e ∈ (κ1 ~ κ0)
    )

  (* Really unsure of these as faithful to cylindrical logic *)
  | judge_cast_pos =>
    sup '(Γ, κ0, κ1, τ, e0, e1), (
      [Γ ⊢ e0 ∈ (κ0 ~ κ1) ;
       Γ ⊢ e1 ∈ (◇ κ0, τ) ]
      ————
      Γ ⊢ cast_pos e0 e1 ∈ (◇ κ1, τ)
    )
  | judge_cast_nec =>
    sup '(Γ, κ0, κ1, τ, e0, e1), (
      [Γ ⊢ e0 ∈ (κ0 ~ κ1) ;
       Γ ⊢ e1 ∈ (□ κ0, τ) ]
      ————
      Γ ⊢ cast_nec e0 e1 ∈ (□ κ1, τ)
    )
  end.

Inductive proof α: list (ofty α) → Type :=
| QED: proof α []
| andso
    {T}
    (r: judgement)
    (s: judge α r)
  :
    proof α (tail (π (judge α r) s) ++ T) →
    proof α (head (π (judge α r) s) :: T).

Arguments QED {α}.
Arguments andso {α T}.

Notation "A # B ; C" := (andso A B C) (at level 60, right associativity,
                                      format "A  #  B  ; '//' C").

Example proof_tt α: proof α [mt ⊢ tt ∈ unit] :=
  judge_tt # _ ;
  QED.

Example proof_compose α κ: proof α [mt ⊢ id κ ∘ id κ ∈ (κ ~ κ)]
  :=
    judge_compose # (mt, κ, κ, κ, id κ, id κ) ;
    judge_id # (mt, κ) ;
    judge_id # (mt, κ) ;
    QED.

Example proof_id α A: proof α [mt ⊢ lam "x" A (var "x") ∈ [A, A]]
  :=
  judge_lam # (mt, A, A, "x", var "x") ;
  judge_var_head # (mt, "x", A) ;
  QED.

Example proof_const α A B: proof α [mt ⊢ lam "x" A (lam "y" B (var "x")) ∈ [A, [B, A]]] :=
  judge_lam # (mt, A, [B, A], "x", lam "y" B (var "x")) ;
  judge_lam # (_, B, A, "y", var "x") ;
  judge_var_tail # ("y", B, _, "x", A) ;
  judge_var_head # (mt, "x", A) ;
  QED.

Example proof_nec_tt α κ: proof α [mt ⊢ necessity κ tt ∈ □ κ, unit] :=
  judge_necessity # (mt, κ, unit, tt) ;
  judge_tt # mt ;
  QED.

Definition find {α} (x: string) (σ: list string) (Γ: ns (sort α) (List.length σ)) : option (sort α).
  induction σ as [|y T].
  - apply None.
  - cbn in *.
    case (String.eqb x y).
    + apply (Some (fst Γ)).
    + apply (IHT (snd Γ)).
Defined.

Definition lookup {α} x (Γ: ctx α) := find x (σ Γ) (ty Γ).

Section infer.
  Context {α: Type} (eq_dec: forall (κ0 κ1: α), {κ0 = κ1} + {κ0 ≠ κ1}).
  Definition sort_eq (x y: sort α): {x = y} + {x ≠ y}.
    decide equality.
  Defined.

  Fixpoint infer (Γ: ctx α) (e: tm α): option (sort α) :=
    match e with
    | var x => lookup x Γ

    | lam x τ0 e =>
      match infer ((x :: σ Γ) |-> (τ0, ty Γ)) e with
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

    | ⟨ e0, e1 ⟩ =>
      match (infer Γ e0, infer Γ e1) with
      | (Some τ0, Some τ1) => Some (prod τ0 τ1)
      | _ => None
      end

    | π1 e =>
      match infer Γ e with
      | Some (prod τ0 τ1) => Some τ0
      | _ => None
      end

    | π2 e =>
      match infer Γ e with
      | Some (prod τ0 τ1) => Some τ1
      | _ => None
      end

    | necessity κ e =>
      match infer mt e with
      | Some τ => Some (□ κ, τ)
      | _ => None
      end

    (* | nec_comm (e: tm) *)

    (* | ext (κ: α) (e: tm) *)
    (* | dup (e: tm) *)

    (* | pos_comm (e: tm) *)
    (* | box (κ: α) (e: tm) *)
    (* | bind (e0: tm) (x: string) (e1: tm) *)

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


    (* | cast_pos (e0 e1: tm) *)
    (* | cast_nec (e0 e1: tm) *)
    | _ => None
    end.
End infer.

Record heap α := { top: nat ; read: nat → tm α ;}.
Arguments top {α}.
Arguments read {α}.

Definition alloc {α} (σ: heap α) (e: tm α): nat * heap α :=
  let ix := top σ in
  (ix, {| top := S ix ; read n := if Nat.eqb n ix then e else read σ n |}).
(* FIXME just do the damn substitution *)
Record big α := big_intro {
  env: list (string * nat) ;
  from: heap α * tm α;
  to: heap α * tm α;
}.
Arguments big_intro {α}.
Arguments env {α}.
Arguments from {α}.
Arguments to {α}.

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

Definition reduce α (l: label): bundle (prop (big α)) :=
  match l with
(* FIXME environment/store is probably all wrong :( *)
  | label_var_head =>
    sup '(Γ, σ, x, n), (
      []
      ————
      (x, n) :: Γ ⊨ (σ, var x) ⇓ (σ, read σ n)
    )
  | label_var_tail =>
    sup '(Γ, H, x, σ, e), (
      [Γ ⊨ (σ, var x) ⇓ (σ, e)]
      ————
      H :: Γ ⊨ (σ, var x) ⇓ (σ, e)
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
      Γ ⊨ (σ, ⟨ e0, e1 ⟩) ⇓ (σ, ⟨ e0 , e1 ⟩)
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
        (x, ix) :: Γ ⊨ (σ1', e2) ⇓ (σ2, e3)
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
        (x, ix) :: Γ ⊨ (σ1', e1) ⇓ (σ2, e3)
      )
      ]
      ————
      Γ ⊨ (σ0, bind e0 x e1) ⇓ (σ2, e3)
    )

  | label_π1_fanout =>
    sup '(Γ, σ0, σ1, e0, e1, e2), (
      [Γ ⊨ (σ0, e0) ⇓ (σ1, ⟨e1, e2⟩) ]
      ————
      Γ ⊨ (σ0, π1 e0) ⇓ (σ1, e1)
    )
  | label_π2_fanout =>
    sup '(Γ, σ0, σ1, e0, e1, e2), (
      [Γ ⊨ (σ0, e0) ⇓ (σ1, ⟨e1, e2⟩) ]
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
    seq α (tail (π (reduce α r) s) ++ T) →
    seq α (head (π (reduce α r) s) :: T).

Arguments HALT {α}.
Arguments step {α T}.

Notation "A @ B ; C" := (step A B C) (at level 60, right associativity,
                                      format "A  @  B  ; '//' C").

Example seq_id α κ σ: seq α [[] ⊨ (σ, id κ ∘ id κ) ⇓ (σ, id κ)] :=
  label_compose_id @ ([], σ,σ,σ, κ, id κ, id κ) ;
  label_id @ ([], σ, κ) ;
  label_id @ ([], σ, κ) ;
  HALT.

Example seq_sym α κ σ: seq α [[] ⊨ (σ, sym (id κ)) ⇓ (σ, id κ)]
  :=
  label_sym_id @ ([], σ, σ, κ, id κ) ;
  label_id @ ([], σ, κ) ;
  HALT.
