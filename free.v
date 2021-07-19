Require Import Coq.Unicode.Utf8.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Inductive free {X} :=
| η (x: X)
| top
| bot
| impl (A B: free)
| and (A B: free)
| or (A B: free)
| path (A B: free)
.

Arguments free: clear implicits.
Notation "⊤" := top.
Notation "⊥" := bot.
Infix "∧" := and.
Infix "∨" := or.
Notation "[ A , B ]" := (impl A B).

Infix "=" := path.

Reserved Notation "A ⊢ B" (at level 80).

Inductive entails {X}: free X → free X → Type :=
| id A: A ⊢ A
| compose {A B C}:
    B ⊢ C → A ⊢ B → A ⊢ C

| bang A: A ⊢ ⊤
| fanout {A B C}:
    C ⊢ A → (C ⊢ B) →
    C ⊢ (A ∧ B)
| π1 A B: (A ∧ B) ⊢ A
| π2 A B: (A ∧ B) ⊢ B

| absurd A: ⊥ ⊢ A
| fanin {A B C}:
    A ⊢ C → (B ⊢ C) →
    (A ∨ B) ⊢ C
| i1 A B: A ⊢ (A ∨ B)
| i2 A B: B ⊢ (A ∨ B)

| cur {A B C}:
    (A ∧ B) ⊢ C → B ⊢ [A, C]
| ev A B:
    (A ∧ [A,  B]) ⊢ B

| refl A: ⊤ ⊢ (A = A)
| trans {A B C}:
    ((B = C) ∧ (A = B)) ⊢ (A = C)
| sym {A B} : (A = B) ⊢ (B = A)

(* FIXME in general not well-founded *)
| J {x y} P:
    (x = y ∧ P x) ⊢ P y
where "A ⊢ B" := (entails A B)
.

Infix "∘" := compose (at level 30).
Notation "!" := bang.
Notation "⁻¹" := sym.

Notation "⟨ x , y , .. , z ⟩" := (fanout .. (fanout x y) .. z).
Notation "[ x ; y ; .. ; z ⟩" := (fanin .. (fanin x y) .. z).

Definition simple {A} (x y: free A) (p: ⊤ ⊢ x = y) (q: ⊤ ⊢ x): ⊤ ⊢ y.
Proof.
  apply (J (λ x, x) ∘ ⟨ p, q ⟩).
Defined.

Definition reverse {A} (x y: free A) (p: ⊤ ⊢ y = x) (q: ⊤ ⊢ x): ⊤ ⊢ y.
Proof.
  apply (J (λ x, x) ∘ ⟨ ⁻¹ ∘ p, q ⟩).
Defined.

Require Import Coq.Strings.String.

Function subst x s ev :=
  match ev with
  | η y => if string_dec x y then s else ev
  | [A, B] => [subst x s A, subst x s B]
  | A ∧ B => subst x s A ∧ subst x s B
  | A ∨ B => subst x s A ∨ subst x s B
  | A = B => subst x s A = subst x s B
  | _ => ev
  end.

Notation "'[' x := u ']' v" := (subst x u v) (at level 1).
