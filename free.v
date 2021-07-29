Require Import Coq.Unicode.Utf8.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Reserved Notation "⟨ x , y , .. , z ⟩".

Reserved Notation "'some' x .. y , P"
         (at level 200, x binder, y binder, right associativity,
          format "'[ ' '[ ' 'some'  x .. y ']' ,  '/' P ']'").
Reserved Notation "'Σ' x .. y , P"
         (at level 200, x binder, y binder, right associativity,
          format "'[ ' '[ ' 'Σ'  x .. y ']' ,  '/' P ']'").

Record someT [A] (P: A → Type) := some_intro { head: A ; tail: P head ; }.

Arguments some_intro [A P].
Arguments head [A P].
Arguments tail [A P].

Module Import SomeNotations.
  Add Printing Let someT.

  Notation "'some' x .. y , P" := (someT (λ x, .. (someT (λ y,  P)) .. )) : type_scope.
  Notation "'Σ' x .. y , P" := (someT (λ x, .. (someT (λ y,  P)) .. )) : type_scope.
  Notation "⟨ x , y , .. , z ⟩" := (some_intro .. (some_intro x y) .. z) : core_scope.
End SomeNotations.

Record iso A B := {
  to: A → B ;
  from: B → A ;
  to_from x: to (from x) = x ;
  from_to x: from (to x) = x ;
}.

Arguments to {A B}.
Arguments from {A B}.

Inductive sort :=
| empty | unit
| sum (A B: sort)
| prod (A B: sort)
| exp (A B: sort)
| Forall (κ: string) (A: sort)
| Forsome (κ: string) (A: sort)
| diag (κ μ: string)
| basechange (p: (string → Type) → (string → Type)) (x: sort)
.

Inductive term: sort → sort → Type :=
| id A: term A A
| compose {A B C}: term B C → term A B → term A C

| bang {A}: term A unit
| fanout {A B C}: term C A → term C B → term C (prod A B)
| π1 {A B}: term (prod A B) A
| π2 {A B}: term (prod A B) B

| absurd {A}: term empty A
| fanin {A B C}: term A C → term B C → term (sum A B) C
| i1 {A B}: term A (sum A B)
| i2 {A B}: term B (sum A B)

| curry {A B C}: term (prod A B) C → term B (exp A C)
| ev {A B}: term (prod A (exp A B)) B

| map_Forsome {A B κ}: term A B → term (Forsome κ A) (Forsome κ B)
| pure {A κ}: term A (Forsome κ A)
| join {A κ}: term (Forsome κ (Forsome κ A)) (Forsome κ A)
| swap_Forsome {A κ μ}: κ ≠ μ → term (Forsome κ (Forsome μ A)) (Forsome μ (Forsome κ A))

| necessity {A κ}: term unit A → term unit (Forall κ A)
| map_Forall {A B κ}: term A B → term (Forall κ A) (Forall κ B)
| mon {A B κ}: term (prod (Forall κ A) (Forall κ B)) (Forall κ (prod A B))
| extract {A κ}: term (Forall κ A) A
| dup {A κ}: term (Forall κ A) (Forall κ (Forall κ A))
| swap_Forall {A κ μ}:
    κ ≠ μ → term (Forall κ (Forall μ A)) (Forall μ (Forall κ A))

| refl κ: term unit (diag κ κ)
| trans {i j k}: term (prod (diag i j) (diag j k)) (diag i k)
.

Infix "∘" := compose (at level 30).

Definition put (Γ: string → Type) (κ: string) (v: Type) (μ: string): Type :=
  if string_dec κ μ
  then
    v
  else
    Γ μ.

Lemma put_redundant {κ Γ}: put Γ κ (Γ κ) = Γ.
Proof.
  extensionality x.
  unfold put.
  destruct (string_dec κ x).
  all: subst.
  all: reflexivity.
Qed.

Lemma put_put {κ Γ x y}: put (put Γ κ x) κ y = put Γ κ y.
Proof.
  extensionality μ.
  unfold put.
  destruct (string_dec κ μ).
  all: subst.
  all: reflexivity.
Qed.

Lemma put_swap {κ μ Γ x y}:
  κ ≠ μ → put (put Γ κ x) μ y = put (put Γ μ y) κ x.
Proof.
  intro p.
  extensionality ν.
  unfold put.
  destruct (string_dec μ ν) eqn:q, (string_dec κ ν) eqn:r.
  all: subst.
  all: try reflexivity.
  contradiction.
Qed.

(*
 Sorts are interpreted as multi-profunctors over a groupoid [xs,V] → Set ?
 Dealing with variance is a massive pain.
*)

Fixpoint op (S: sort) (Γ: string → Type): Type :=
  match S with
  | empty => False
  | unit => True
  | sum A B => op A Γ + op B Γ
  | prod A B => op A Γ * op B Γ
  | exp A B => ∀ Δ, (∀ s, Δ s → Γ s) → op A Δ → op B Δ

  (* Still really confused about this part.  I think other sources
     might complicate it because they have to do a relation variant of
     put?  *)
  | Forall κ A => ∀ v, op A (put Γ κ v)
  | Forsome κ A => Σ v, op A (put Γ κ v)
  | diag κ μ => ∀ Δ, (∀ s, Δ s → Γ s) → Δ κ → Δ μ
  | basechange p x => ∀ Δ, (∀ s, p Δ s → Γ s) → op x Δ
  end.

(* Not even so important ? *)

Definition map (S: sort) {Γ Δ: string → Type} (f: ∀ κ, Δ κ → Γ κ): op S Γ → op S Δ.
Proof.
  generalize dependent Δ.
  generalize dependent Γ.
  induction S.
  all: intros Γ Δ f x.
  - cbn in *.
    contradiction.
  - cbn in *.
    exists.
  - cbn in *.
    destruct x as [x'|x'].
    + left.
      apply (IHS1 Γ Δ f x').
    + right.
      apply (IHS2 Γ Δ f x').
  - cbn in *.
    apply (IHS1 Γ Δ f (fst x), IHS2 Γ Δ f (snd x)).
  - cbn in *.
    intros Δ' p y.
    apply (x Δ').
    + intros ? ?.
      apply f.
      apply p.
      auto.
    + auto.
  - cbn in *.
    intros ?.
    apply (IHS (put Γ κ v)).
    + intros.
      unfold put in *.
      destruct (string_dec κ κ0).
      * auto.
      * apply f.
        auto.
    + apply x.
  - cbn in *.
    destruct x as [h x].
    exists h.
    apply (IHS (put Γ κ h)).
    + intros.
      unfold put in *.
      destruct (string_dec κ κ0).
      * auto.
      * apply f.
        auto.
    + apply x.
  - cbn in *.
    intros ? p y.
    apply x.
    + intros ? z.
      apply f.
      apply p.
      auto.
    + auto.
  - cbn in *.
    intros.
    apply (IHS Δ0).
    + intros.
      auto.
    + apply x.
      intros.
      apply f.
      apply X.
      auto.
Defined.

Definition eval {A B} (t: term A B) {κ}: op A κ → op B κ.
Proof.
  generalize dependent κ.
  induction t.
  all: intros Γ x.
  - apply x.
  - apply IHt1.
    apply IHt2.
    auto.
  - cbn in *.
    exists.
  - cbn in *.
    split.
    + apply IHt1.
      auto.
    + apply IHt2.
      auto.
  - apply x.
  - apply x.
  - cbn in x.
    contradiction.
  - cbn in *.
    destruct x as [x' | x'].
    + apply IHt1.
      auto.
    + apply IHt2.
      auto.
  - cbn in *.
    left.
    auto.
  - cbn in *.
    right.
    auto.
  - cbn in *.
    intros Δ p y.
    apply (IHt Δ).
    refine (y, _).
    apply (map _ p x).
  - destruct x as [x f].
    cbn in f.
    refine (f _ _ x).
    intros.
    auto.
  - cbn in *.
    exists (head x).
    apply IHt.
    apply (tail x).
  - cbn in *.
    exists (Γ κ).
    rewrite put_redundant.
    auto.
  - destruct x as [h [h' t]].
    cbn in *.
    exists h'.
    rewrite put_put in t.
    auto.
  - destruct x as [h [h' t]].
    cbn in *.
    exists h'.
    exists h.
    auto.
    rewrite put_swap.
    1: auto.
    auto.
  - cbn in *.
    intro v.
    apply IHt.
    apply x.
  - cbn in *.
    intro v.
    apply IHt.
    apply x.
  - cbn in *.
    destruct x as [x y].
    intro v.
    apply (x v, y v).
  - cbn in x.
    set (x' := x (Γ κ)).
    rewrite put_redundant in x'.
    auto.
  - cbn in *.
    intros.
    rewrite put_put.
    apply x.
  - cbn in *.
    intros.
    rewrite put_swap.
    2:auto.
    apply x.
  - cbn.
    intros.
    apply X0.
  - cbn in *.
    destruct x as [f g].
    intros Δ p y.
    apply g.
    1: apply p.
    apply f.
    1: apply p.
    auto.
Defined.

