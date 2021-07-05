Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector.
Require Import Coq.Bool.Bool.
Require Coq.Structures.OrdersAlt.
Require Coq.Structures.OrderedTypeEx.
Require Coq.MSets.MSetAVL.
Require Coq.MSets.MSetInterface.

Import IfNotations.
Import ListNotations.
Open Scope string_scope.

Close Scope nat.

Module String_as_OT := OrdersAlt.Update_OT OrderedTypeEx.String_as_OT.
Module S <: MSetInterface.S := MSetAVL.Make String_as_OT.

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

Fixpoint free {α} (t: tm α): S.t :=
  match t with
  | var x => S.singleton x

  | lam x _ e => S.remove x (free e)

  | app e0 e1 => S.union (free e0) (free e1)

  | fanout e0 e1 => S.union (free e0) (free e1)
  | π1 e => free e
  | π2 e => free e

  | necessity _ e => free e

  | nec_comm e => free e

  | ext _ e => free e
  | dup e => free e

  | pos_comm e => free e

  | box _ e => free e

  | bind e0 x e1 => S.union (free e0) (S.remove x (free e1))

  | compose e0 e1 => S.union (free e0) (free e1)

  | sym e => free e

  | cast_pos e0 e1 => S.union (free e0) (free e1)
  | cast_nec e0 e1 => S.union (free e0) (free e1)

  | _ => S.empty
  end.

Definition ns (A: Type): nat → Type :=
  fix loop n :=
    match n with
    | O => True
    | S n' => A * loop n'
    end.


Record map V := map_intro {
  keys: S.t ;
  vals s: S.In s keys → V ;
}.

Arguments map_intro {V}.
Arguments keys {V}.
Arguments vals {V}.

Notation "A |-> B" := (map_intro A B) (at level 30).

#[program]
Definition mt {V}: map V := S.empty |-> λ s p, _.

Next Obligation.
Proof.
  set (abs := S.empty_spec p).
  contradiction.
Defined.

#[program]
Definition put {V} (x: string) (v: V) (m: map V): map V :=
  S.add x (keys m) |-> λ y p, if string_dec y x then v else vals m y _.

Next Obligation.
Proof.
  destruct (S.add_spec (keys m) x y) as [l r].
  destruct (l p).
  - contradiction.
  - assumption.
Qed.

(* Pretty hacky *)
#[program]
Lemma query (x: string) (s: S.t): { S.mem x s = true } + { S.mem x s ≠ true}.
Proof.
  set (bit := S.mem x s).
  destruct bit.
  - left.
    reflexivity.
  - right.
    discriminate.
Defined.

Definition get {V} (x: string) (m: map V): option V :=
  match query x (keys m) with
  | left p => Some (vals m x (proj1 (S.mem_spec (keys m) _) p))
  | _ => None
  end.

Definition ctx α := map (sort α).

Record ofty α := ofty_intro {
  Γ: ctx α;
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
      consequent: A ;
      antecedent: list A ;
    }.
Arguments impl {A}.
Arguments consequent {A}.
Arguments antecedent {A}.

Notation "P ———— Q" := (impl Q P).

Variant judgement :=
| judge_var

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

(* A bit of a hack tbh *)
Variant inmap α := imap (Γ: ctx α) (x: string) (p: S.mem x (keys Γ) = true).
Arguments imap {α}.

Definition judge α (r: judgement): bundle (prop (ofty α)) :=
  match r with
  | judge_var =>
    sup '(imap Γ x p), (
      []
      ————
      Γ ⊢ var x ∈ vals Γ x (proj1 (S.mem_spec (keys Γ) _) p)
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
      Γ ⊢ fanout e0 e1 ∈ (τ0 × τ1)
    )
  | judge_fst =>
    sup '(Γ, τ0, τ1, e), (
      [Γ ⊢ e ∈ (τ0 × τ1) ]
      ————
      Γ ⊢ π1 e ∈ τ0
    )
  | judge_snd =>
    sup '(Γ, τ0, τ1, e), (
      [ Γ ⊢ e ∈ (τ0 × τ1) ]
      ————
      Γ ⊢ π2 e ∈ τ1
    )

  | judge_lam =>
    sup '(Γ, τ0, τ1, x, e), (
      [ put x τ0 Γ ⊢ e ∈ τ1]
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
    sup '( κ, τ, e, Γ ), (
      [Γ ⊢ e ∈ (□ κ, τ)]
      ————
      Γ ⊢ ext κ e ∈ τ
    )
  | judge_dup =>
    sup '( Γ, κ, τ, e ), (
      [Γ ⊢ e ∈ (□ κ, τ)]
      ————
      Γ ⊢ dup e ∈ (□ κ, □ κ, τ)
    )

  | judge_pos_comm =>
    sup '( κ0, κ1, τ, e, Γ ), (
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
      put x τ0 Γ ⊢ e1 ∈ (□ κ, τ1)]
      ————
      Γ ⊢ bind e0 x e1 ∈ (□ κ, τ1)
    )

  | judge_id =>
    sup '( Γ, κ), (
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
    proof α (antecedent (π (judge α r) s) ++ T) →
    proof α (consequent (π (judge α r) s) :: T).

Arguments QED {α}.
Arguments andso {α T} r s &.

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

#[program]
Example proof_id α A: proof α [mt ⊢ lam "x" A (var "x") ∈ [A, A]] :=
  judge_lam # (mt, A, A, "x", var "x") ;
  judge_var # imap _ "x" _ ;
  QED.

#[program]
Example proof_const α A B: proof α [mt ⊢ lam "x" A (lam "y" B (var "x")) ∈ [A, [B, A]]] :=
  judge_lam # (mt, A, [B, A], "x", lam "y" B (var "x")) ;
  judge_lam # (_, B, A, "y", var "x") ;
  judge_var # imap _ "x" _ ;
  QED.

Example proof_nec_tt α κ: proof α [mt ⊢ necessity κ tt ∈ □ κ, unit] :=
  judge_necessity # (mt, κ, unit, tt) ;
  judge_tt # mt ;
  QED.

Section infer.
  Context {α: Type} (eq_dec: forall (κ0 κ1: α), {κ0 = κ1} + {κ0 ≠ κ1}).
  Definition sort_eq (x y: sort α): {x = y} + {x ≠ y}.
    decide equality.
  Defined.

  Fixpoint infer (Γ: ctx α) (e: tm α): option (sort α) :=
    match e with
    | var x => get x Γ

    | lam x τ0 e =>
      match infer (put x τ0 Γ) e with
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
        match infer (put x τ0 Γ) e1 with
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


    (* | cast_pos (e0 e1: tm) *)
    (* | cast_nec (e0 e1: tm) *)
    | _ => None
    end.

  Lemma infer_proof Γ e τ (p: proof α [Γ ⊢ e ∈ τ]): infer Γ e = Some τ.
  Proof.
    admit.
  Admitted.
End infer.

Record heap α := { top: nat ; read: nat → tm α ;}.
Arguments top {α}.
Arguments read {α}.

Definition alloc {α} (σ: heap α) (e: tm α): nat * heap α :=
  let ix := top σ in
  (ix, {| top := S ix ; read n := if Nat.eqb n ix then e else read σ n |}).
(* FIXME just do the damn substitution *)

Definition environ := map nat.
Record big α := big_intro {
  env: environ ;
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
Definition load (x: string) (Γ: environ): nat :=
  if get x Γ is Some n then n else O.

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
        put x ix Γ ⊨ (σ1', e2) ⇓ (σ2, e3)
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
        put x ix Γ ⊨ (σ1', e1) ⇓ (σ2, e3)
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

Example seq_id α κ σ: seq α [mt ⊨ (σ, id κ ∘ id κ) ⇓ (σ, id κ)] :=
  label_compose_id @ (mt, σ,σ,σ, κ, id κ, id κ) ;
  label_id @ (mt, σ, κ) ;
  label_id @ (mt, σ, κ) ;
  HALT.

Example seq_sym α κ σ: seq α [mt ⊨ (σ, sym (id κ)) ⇓ (σ, id κ)]
  :=
  label_sym_id @ (mt, σ, σ, κ, id κ) ;
  label_id @ (mt, σ, κ) ;
  HALT.
