#[global]
Set Primitive Projections.
#[global]
Unset Printing Primitive Projection Parameters.

#[global]
Set Universe Polymorphism.

#[global]
Set Default Goal Selector "!".

Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import IfNotations.
Import ListNotations.

Close Scope nat.

Reserved Notation "⟨ x , y , .. , z ⟩".

Reserved Notation "'some' x .. y , P"
         (at level 200, x binder, y binder, right associativity,
          format "'[ ' '[ ' 'some'  x .. y ']' ,  '/' P ']'").
Reserved Notation "'Σ' x .. y , P"
         (at level 200, x binder, y binder, right associativity,
          format "'[ ' '[ ' 'Σ'  x .. y ']' ,  '/' P ']'").

#[universes(cumulative)]
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

(* An idea of what Polynomial endoprofunctors might be *)
Record Poly := {
  pos: Type ;
  forward: pos → Type ;
  backward: pos → Type ;
}.

Inductive w (H: Poly) A :=
| sup s
      (f: forward H s → w H A)
      (b: A → backward H s).

Arguments sup {H A} s &.

Definition wmap {A B}
           (f: pos A → pos B)
           (g: ∀ t, forward B (f t) → forward A t)
           (h: ∀ t, backward A t → backward B (f t))
           {x} (p: w A x): w B x.
  induction p.
  exists (f s).
  - intro.
    apply X.
    apply g.
    auto.
  - intro.
    apply h.
    apply b.
    auto.
Defined.

Definition id: Poly := {| forward (_: unit) := unit ; backward _ := unit |}.

Definition const A: Poly := {| forward (_: A) := Empty_set ; backward _ := unit |}.

Definition extract {A x} (p: w (const A) x): A :=
  let '(sup s _ _) := p in s.

(* FIXME figure out induction *)

Definition Π {A} (p: A → Poly): Poly :=
  {|
  pos := ∀ i, pos (p i) ;
  forward s := Σ i, forward (p i) (s i) ;
  (* I suspect I want the opposite thing here but am far from sure *)
  backward s := ∀ i, backward (p i) (s i) ;
  |}.
Definition Sum {A} (p: A → Poly): Poly :=
  {|
  pos := Σ i, pos (p i) ;
  forward s := forward (p (head s)) (tail s) ;
  backward s := backward (p (head s)) (tail s) ;
  |}.

Definition prod (p q: Poly): Poly :=
  {|
  pos := pos p * pos q ;
  forward '(x, y) := forward p x + forward q y ;
  (* I suspect I want the opposite coproduct here *)
  backward '(x, y) := backward p x * backward q y ;
  |}.

Definition sum (p q: Poly): Poly :=
  {|
  pos := pos p + pos q ;
  forward s :=
    match s with
    | inl x' => forward p x'
    | inr x' => forward q x'
    end ;
  backward s :=
    match s with
    | inl x' => backward p x'
    | inr x' => backward q x'
    end ;
  |}.

Infix "*" := prod.
Infix "+" := sum.

(* Simple example *)
Definition listf A := const unit + const A * id.
Definition plist A := w (listf A).

#[program]
Definition constant {A C} :=
  fix loop (l: list C): plist C A :=
    match l with
    | nil =>
      sup (inl tt) (λ x, match x with end) (fun _ => tt)
    | cons H T =>
      let T' := loop T in
      sup (inr (H, tt)) (λ _, T') (λ _, (tt, tt))
    end.

Open Scope nat.

Open Scope string_scope.
Compute constant [ "foo" ; "bar" ; "gar" ].
