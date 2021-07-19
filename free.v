Require Import Coq.Unicode.Utf8.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Declare Scope category_scope.
Declare Scope functor_scope.
Declare Scope morphism_scope.

Delimit Scope category_scope with category.
Delimit Scope functor_scope with functor.
Delimit Scope morphism_scope with morphism.

Inductive category {X} :=
| η (x: X)
| set
| trv
| prod (A B: category)
.

Arguments category: clear implicits.
Bind Scope category_scope with category.

Notation "⊤" := trv.
Infix "*" := prod.

Reserved Notation "A ⊩ B" (at level 80).

Inductive functor {X}: category X → category X → Type :=
| Id A: A ⊩ A
| Compose {A B C}:
    B ⊩ C → A ⊩ B → A ⊩ C

| Bang A: A ⊩ ⊤
| Fanout {A B C}:
    C ⊩ A → (C ⊩ B) →
    C ⊩ (A * B)
| Fst A B: (A * B) ⊩ A
| Snd A B: (A * B) ⊩ B

| Unit: ⊤ ⊩ set
| Empty: ⊤ ⊩ set
| Prod: (set * set) ⊩ set
| Sum: (set * set) ⊩ set
where "A ⊩ B" := (functor A B)
.

Bind Scope functor_scope with functor.

Infix "∘" := Compose (at level 30) : functor_scope.

Notation "!" := Bang : functor_scope.
Notation "⟨ x , y , .. , z ⟩" := (Fanout .. (Fanout x y) .. z) : functor_scope.

Notation "⊤" := Unit : functor_scope.
Notation "⊥" := Empty : functor_scope.

Reserved Notation "A ⊢ B" (at level 80).

Inductive morphism {X}: ∀ {F G: category X}, F ⊩ G → F ⊩ G → Type :=
| id {F G} (A: F ⊩ G) : A ⊢ A
| compose {F G} {A B C: F ⊩ G}:
    B ⊢ C → A ⊢ B → A ⊢ C

| bang {Γ} (A: Γ ⊩ set): A ⊢ (Unit ∘ ! _)
| fanout {Γ} {C A B: Γ ⊩ set}:
    C ⊢ A → C ⊢ B →
    C ⊢ Prod ∘ ⟨A, B⟩
| fst {Γ} {A B: Γ ⊩ set}:
    Prod ∘ ⟨A, B⟩ ⊢ A
| snd {Γ} {A B: Γ ⊩ set}:
    Prod ∘ ⟨A, B⟩ ⊢ B

| absurd {Γ} (A: Γ ⊩ set): (Empty ∘ ! _) ⊢ A
| fanin {Γ} {A B C: Γ ⊩ set}:
    A ⊢ C → B ⊢ C →
    Sum ∘ ⟨A,  B⟩ ⊢ C
| inl {Γ} {A B: Γ ⊩ set}: A ⊢ Sum ∘ ⟨A, B⟩
| inr {Γ} {A B: Γ ⊩ set}: B ⊢ Sum ∘ ⟨A, B⟩
where "A ⊢ B" := (morphism A B)
.

Bind Scope morphism_scope with morphism.

Infix "∘" := compose : morphism_scope.
Notation "!" := bang : morphism_scope.

Notation "⟨ x , y , .. , z ⟩" := (fanout .. (fanout x y) .. z) : morphism_scope.
Notation "[ x ; y ; .. ; z ]" := (fanin .. (fanin x y) .. z) : morphism_scope.

Example diag {X} {Γ: category X} (A: Γ ⊩ set): A ⊢ Prod ∘ ⟨A, A⟩ :=
  ⟨ id _,  id _ ⟩.
