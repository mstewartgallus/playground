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
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Psatz.
Require Import Recdef.

Import IfNotations.
Import ListNotations.

Close Scope nat.

Reserved Notation "'some' x .. y , P"
         (at level 200, x binder, y binder, right associativity,
          format "'[ ' '[ ' 'some'  x .. y ']' ,  '/' P ']'").

#[universes(cumulative)]
Record someT [A] (P: A → Type) := some_intro { head: A ; tail: P head ; }.

Arguments some_intro [A P].
Arguments head [A P].
Arguments tail [A P].

Module SomeNotations.
  Add Printing Let someT.

  Notation "'some' x .. y , P" := (someT (λ x, .. (someT (λ y,  P)) .. )) : type_scope.
End SomeNotations.


Module CylPoly.
  #[universes(cumulative)]
  Record Poly := {
    pos: Type ;
    dir: pos → string → Type ;
  }.

  Coercion pos: Poly >-> Sortclass.

  Definition CoYo (Γ: string → Type) : Poly := {|
    pos := unit ;
    dir _ := Γ ;
  |}.

  Definition K A: Poly := {| dir (_: A) _ := Empty_set |}.

  Definition I: Poly := {|
    pos := unit ;
    dir _ _ := unit  ;
  |}.

  Record ext (P: Poly) (Γ: string → Type) :=
    sup {
        tag: _ ;
        field v: dir P tag v → Γ v ;
      }.

  Arguments sup {P Γ}.
  Arguments tag {P Γ}.
  Arguments field {P Γ}.

  Coercion ext: Poly >-> Funclass.

  Definition map {H: Poly} {A B} (f: ∀ v, A v → B v) (x: H A): H B :=
      sup (tag x) (fun v y => f v (field x v y)).

  Definition Π {A: Type} (p: A → Poly): Poly :=
    {|
    pos := ∀ i, pos (p i) ;
    dir s x := someT (fun i => dir (p i) (s i) x) ;
    |}.
  Definition exp A B := Π (λ _: A, B).

 Definition bind (p: Poly) (q: string → Poly): Poly :=
    {|
    pos := p (λ x, pos (q x)) ;
    dir s x :=
      someT (fun i => dir (q x) (field s x i) x) ;
    |}.

  Definition compose x q p := bind p (λ y, exp (y = x) q).

  Definition Σ {A} (p: A → Poly): Poly :=
    {|
    pos := someT (fun i => pos (p i)) ;
    dir s x := dir (p (head s)) (tail s) x ;
    |}.

  Definition prod (p q: Poly): Poly :=
    {|
    pos := pos p * pos q ;
    dir '(x, y) v := dir p x v + dir q y v ;
    |}.

  Definition sum (p q: Poly): Poly :=
    {|
    pos := pos p + pos q ;
    dir s v :=
      match s with
      | inl x' => dir p x' v
      | inr x' => dir q x' v
      end ;
    |}.


  (* FIXME hacky *)
  Definition V x: Poly := CoYo (λ y, x = y).
  Definition subst (x: string) (A: Type) Γ := λ y, if string_dec x y then A else Γ y.

  Definition scope (x: string) (A: Type) (Γ: string → Type) :=
    λ y, {_: A | x = y } + { _: Γ y | x ≠ y }.

  Definition All x S: Poly := CoYo (λ y, x = y → S).

  Infix "*" := prod.
  Infix "+" := sum.


  (* FIXME not good *)
  Definition diag (x y: string) :=
    Σ (λ (Γ: string → Type), {|
         pos := Γ x → Γ y ;
         dir _ := Γ ;
       |}).

  Infix "~>" := diag (at level 30).

  Inductive w x (p: Poly) (Γ: string → Type) :=
  | rec (_: p (scope x (w x p Γ) Γ)).

  Definition mt := λ _: string, Empty_set.
  Definition put (x: string) (A: Type) Γ := λ y, if string_dec x y then A else Γ y.

  Fixpoint oflist (l: list (string * Type)): string → Type :=
    match l with
    | nil => mt
    | cons (X, A) T => put X A (oflist T)
    end.

  Open Scope string_scope.

  Example plist A := w "x" (K unit + K A * V "x") mt.
  Example pnil {A}: plist A.
  Proof.
    cbn in *.
    exists.
    exists (inl tt).
    cbn in *.
    intros ? ?.
    contradiction.
  Defined.

  Example pcons {A} (h: A) (t: plist A): plist A.
  Proof.
    cbn in *.
    exists.
    exists (inr (h, tt)).
    cbn in *.
    intros ? [?|?].
    1: contradiction.
    subst.
    left.
    exists.
    2: reflexivity.
    apply t.
  Defined.

  Fixpoint poflist {A} (l: list A): plist A :=
    match l with
    | nil => pnil
    | cons H T => pcons H (poflist T)
    end.

  Example foo {A B} (x: A) (y: B): ext (V "x" * V "y") (oflist [("x", A) ; ("y", B)]).
    exists (tt, tt).
    intros ? [?|?].
    all: cbn in *.
    all: subst.
    - apply x.
    - apply y.
  Defined.

  Example gar {A B} (f: A → B): ext ("x" ~> "y") (oflist [("x", A) ; ("y", B)]).
  Proof.
    cbn.
    eexists (some_intro (oflist [("x", A) ; ("y", B)]) _).
    Unshelve.
    2: {
      cbn.
      apply f.
    }
    cbn.
    intros.
    auto.
  Defined.

  Example bar := poflist ["foo" ; "bar" ; "xar"].
End CylPoly.

(* Free monad on a polynomial endofunctor *)
Module Poly.
  #[universes(cumulative)]
   Record Poly := {
    pos: Type ;
    dir: pos → Type ;
  }.

  Coercion pos: Poly >-> Sortclass.

  (* Definition K A: Poly := {| dir (_: A) := Empty_set |}. *)

  Record ext (P: Poly) A :=
    sup {
        tag: _ ;
        field: dir P tag → A ;
      }.

  Arguments sup {P A}.
  Arguments tag {P A}.
  Arguments field {P A}.

  Infix "!" := field (at level 30).

  Coercion ext: Poly >-> Funclass.

  Definition X: Poly := {| dir (_: unit) := unit |}.

  Definition CoYo (A:  Type) : Poly := {|
    pos := unit ;
    dir _ := A ;
  |}.

  Definition compose (p q: Poly): Poly :=
    {|
    pos := p (pos q) ;
    dir s := someT (fun i => dir q (s ! i)) ;
    |}.
  Infix "∘" := compose (at level 30).

  Definition Π {A} (p: A → Poly): Poly :=
    {|
    pos := ∀ i, pos (p i) ;
    dir s := someT (fun i => dir (p i) (s i)) ;
    |}.
  Definition Σ {A} (p: A → Poly): Poly :=
    {|
    pos := someT (fun i => pos (p i)) ;
    dir s := dir (p (head s)) (tail s) ;
    |}.

  Definition prod (p q: Poly): Poly :=
    {|
    pos := pos p * pos q ;
    dir '(x, y) := dir p x + dir q y ;
    |}.

  Definition sum (p q: Poly): Poly :=
    {|
    pos := pos p + pos q ;
    dir s :=
      match s with
      | inl x' => dir p x'
      | inr x' => dir q x'
      end ;
    |}.

  Infix "*" := prod.
  Infix "+" := sum.

  Definition exp A B := Π (λ _: A, B).
End Poly.

Module PolyCat.
  Module Import Cat.
    Inductive Obj := init | term | sum (_ _: Obj) | exp (_ _: Obj).
    Inductive Mor: Obj → Obj → Type :=
    | id A: Mor A A
    | compose {A B C}: Mor B C → Mor A B → Mor A C
    | absurd {A}: Mor init A
    .
  End Cat.

  Module Import Dis.
    Record Dis := {
      pos: Type ;
      dir: pos → Obj ;
    }.

    Record Mor (A B: Dis) := {
      pos_Mor: pos A → pos B  ;
      dir_Mor x: Cat.Mor (dir B (pos_Mor x)) (dir A x) ;
    }.

    Arguments pos_Mor {A B}.
    Arguments dir_Mor {A B}.

    Record ext (P: Dis) (x: Obj) := sup {
       tag: pos P ;
       field: Cat.Mor (dir P tag) x ;
    }.

    Arguments sup {P x}.
    Arguments tag {P x}.
    Arguments field {P x}.

    Coercion ext: Dis >-> Funclass.

    Definition Yo (x: Obj): Dis := {| dir (_: unit) := x |}.
    Definition K (x: Type): Dis := {| dir (_: x) := init |}.

    Definition Π {A} (p: A → Dis): Dis :=
    {|
      pos := A * (∀ i, pos (p i)) ;
      dir '(x, f) := dir (p x) (f x) ;
    |}.

    Definition Σ {A} (p: A → Dis): Dis := {|
      pos := someT (fun i => pos (p i)) ;
      dir s := dir (p (head s)) (tail s) ;
    |}.

    Definition prod (p q: Dis): Dis := {|
      pos := pos p * pos q ;
      dir '(x, y) := sum (dir p x) (dir q y) ;
     |}.

    Definition sum (p q: Dis): Dis := {|
      pos := pos p + pos q ;
      dir v :=
        match v with
        | inl v' => dir p v'
        | inr v' => dir q v'
        end ;
     |}.
  End Dis.

  #[universes(cumulative)]
  Record Poly := {
    pos: Dis ;
    dir: Dis.Mor pos {| pos := Dis ; dir _ := init ; |} ;
  }.

  #[program]
  Definition X: Poly := {|
    pos := Yo term ;
    dir := {|
            pos_Mor _ := Yo term ;
            dir_Mor _ := absurd ;
           |} ;
  |}.

  #[program]
  Definition CoYo (A: Dis) : Poly := {|
    pos := Yo term  ;
    dir := {|
            pos_Mor _ := A ;
            dir_Mor _ := absurd ;
          |}
  |}.

  (* Definition comp (p q: Poly): Poly := *)
  (*   {| *)
  (*   pos := p (pos q) ; *)
  (*   dir s := someT (fun i => dir q (field s i)) ; *)
  (*   |}. *)
  (* Infix "∘" := compose (at level 30). *)

  #[program]
  Definition Σ {A} (p: A → Poly): Poly :=
    {|
    pos := Σ (fun i => pos (p i)) ;
    dir :=
      {|
        pos_Mor x := pos (p (head x)) ;
        dir_Mor x := _ ;
       |}
    |}.

  #[program]
  Definition Π {A} (p: A → Poly): Poly :=
    {|
    pos := Π (λ i, pos (p i)) ;
    dir := {|
            pos_Mor '(x, f) := _ ;
          |}
  |}.

  Next Obligation.
  Proof.
    cbn in *.
    apply (dir (p (head x))).
  Defined.

  #[program]
  Definition K A: Poly := {|
    pos := A ;
    dir := {|
            pos_Mor _ := Yo init ;
            dir_Mor _ := absurd ;
          |} ;
  |}.


  #[program]
  Definition prod (p q: Poly): Poly :=
    {|
     pos := Dis.prod (pos p) (pos q) ;
     dir :=
       {|
         pos_Mor '(x, y) := Yo (Cat.sum (Dis.dir (pos p) x) (Dis.dir (pos q) y)) ;
         dir_Mor _ := absurd ;
       |} ;
    |}.

  #[program]
  Definition sum (p q: Poly): Poly :=
    {|
    pos := sum (pos p) (pos q) ;
    dir :=
      {|
        pos_Mor v :=
          match v with
          | inl v' => Yo (Dis.dir (pos p) v')
          | inr v' => Yo (Dis.dir (pos q) v')
          end ;
        dir_Mor _ := absurd ;
      |}
    |}.

  Infix "*" := prod.
  Infix "+" := sum.

  (* Definition exp A B := Π (λ _: A, B). *)
End PolyCat.

Module Span.
  #[universes(cumulative)]
   Record span A B := {
    s: Type ;
    π1: s → A ;
    π2: s → B ;
  }.

  Arguments s {A B}.
  Arguments π1 {A B}.
  Arguments π2 {A B}.
  Coercion s: span >-> Sortclass.

  Definition id A: span A A := {| π1 x := x ; π2 x := x |}.
  Definition compose {A B C} (f: span B C) (g: span A B) := {|
    s := { xy : s f * s g | π1 f (fst xy) = π2 g (snd xy) } ;
    π1 x := π1 g (snd (proj1_sig x)) ;
    π2 x := π1 f (fst (proj1_sig x)) ;
  |}.

  Infix "∘" := compose (at level 30).

  #[universes(cumulative)]
  Class Span_Mor {A B} {s: span A B} {t: span A B} (f: s → t) := {
    map_π1 x: π1 t (f x) = π1 s x ;
    map_π2 x: π2 t (f x) = π2 s x ;
  }.

  Inductive ext {A B} (p: span A B): A → B → Type :=
  | sup x : ext p (π1 p x) (π2 p x).

  Coercion ext: span >-> Funclass.


  Definition map {A B} (f: A → B): span A B :=
    {| π1 x := x ;
       π2 := f ;
     |}.

  Definition K {A B} (x: A) (y: B): span A B :=
    {|
    s := unit ;
    π1 _ := x ;
    π2 _ := y ;
    |}.

  Definition transpose {A B} (p: span A B): span B A :=
    {|
    s := s p ;
    π1 := π2 p ;
    π2 := π1 p ;
    |}.

  Definition sum {A B} (p q: span A B): span A B :=
    {|
    s := s p + s q ;
    π1 s :=
      match s with
      | inl x' => π1 p x'
      | inr x' => π1 q x'
      end ;
    π2 s :=
      match s with
      | inl x' => π2 p x'
      | inr x' => π2 q x'
      end ;
    |}.

  Definition Σ {B C} {A: span B C} (p: A → span B C): span B C :=
    {|
    s := someT (fun i => s (p i)) ;
    π1 s := π1 (p (head s)) (tail s) ;
    π2 s := π2 (p (head s)) (tail s) ;
    |}.


  Definition prod {A B} (f g: span A B): span A B :=
    {|
    s := { xy : s f * s g |
           π1 f (fst xy) = π1 g (snd xy) ∧
           π2 f (fst xy) = π2 g (snd xy)
         } ;
    π1 s := π1 f (fst (proj1_sig s)) ;
    π2 s := π2 f (fst (proj1_sig s)) ;
    |}.

  (* Not sure about this *)
  Definition Π {B C} {A} (p: A → span B C): span B C :=
    {|
    s := { xy :
             A *
             (∀ i, s (p i)) |
           (∀ i j,
           π1 (p i) (snd xy i) = π1 (p j) (snd xy j) ∧
           π2 (p i) (snd xy i) = π2 (p j) (snd xy j))
         } ;
    π1 s :=
      let y := fst (proj1_sig s) in
      π1 (p y) (snd (proj1_sig s) y) ;
    π2 s :=
      let y := fst (proj1_sig s) in
      π2 (p y) (snd (proj1_sig s) y) ;
    |}.

  Record Poly B C := {
    S: span B C ;
    π: S → Type ;
  }.

  #[program]
  Definition poly {B C} (S: span B C) (p: S → span B C) (X: span B C) :=
    Σ (λ y: S,
            {|
              s := p y → X ;
              π1 f := _ ;
              π2 f := _ ;
            |}).

  Next Obligation.
  Check poly.
  Infix "∧" := prod.
  Infix "∨" := sum.

  Check poly.
  Notation "'Σ' x .. y , P" := (Σ (λ x, .. (Σ (λ y,  P)) .. ))
         (at level 200, x binder, y binder, right associativity,
          format "'[ ' '[ ' 'Σ'  x .. y ']' ,  '/' P ']'").
End Span.
Module Stlc.
  Import Span.


  Inductive sort :=
  | pt
  | exp (τ0 τ1: sort).

  Inductive term :=
  | lam (x: string) (τ: sort) (e: term)
  | app (e0 e1: term)
  | var (x: string)
  .

  Definition env := list (string * sort).

  Inductive fact := ofty (Γ: env) (e: term) (τ: sort).
  Notation "Γ ⊢ e ∈ τ" := (ofty Γ e τ) (at level 30).

  Example judge: span (list fact) (list fact) :=
    Σ A,
      K A [] ∨
    Σ A B T,
      K (A :: B :: T)
        (B :: A :: T) ∨
    Σ A B T,
      K (A :: B :: T)
        (A :: T) ∨
    Σ A B T,
      K (A :: B :: T)
        (B :: T) ∨
    Σ Γ e τ T,
      K (Γ ⊢ e ∈ τ :: T)
        (Γ ⊢ e ∈ τ :: T)
  .

  Inductive rule {Γ: string → fact} :=
  | ignore_rule (A: list fact)
  | swap_rule (T: list fact) (A B: fact)
  | fst_rule (T: list fact) (A B: fact)
  | snd_rule (T: list fact) (A B: fact)

  | lookup_rule (T: list fact) (x: string)
  .
  Arguments rule: clear implicits.

  Example judge (Γ: string → fact) (r: rule Γ): (list fact * list fact) :=
    match r with
    | ignore_rule A =>
      (A,
       [])
    | lookup_rule T x =>
      (T,
       Γ x :: T)
    | swap_rule T A B =>
      (A :: B :: T,
       B :: A :: T)
    | fst_rule T A B =>
      (A :: B :: T,
       A :: T)
    | snd_rule T A B =>
      (A :: B :: T,
       B :: T)
    end.

  Example theory: displayed fact := {|
    map e := {|
              π1 r := fst (judge e r) ;
              π2 r := snd (judge e r) ;
            |} ;
  |}.
  Definition theorem := free theory.

  Example ignore Γ A: theorem Γ A [] := sup (map theory _) (ignore_rule A).
  Example lookup Γ x: theorem Γ [] [Γ x] := sup (map theory _) (lookup_rule [] x).

  Example swap' Γ A B T: theorem Γ (A :: B :: T) (B :: A :: T) := sup (map theory _) (swap_rule T A B).

  Example app' Γ e0 e1 τ0 τ1: free theory _ [_ ; _] [_] := sup (map theory _) (app_rule Γ e0 e1 τ0 τ1).

  Check app'.
  Definition sort_dec (x y: sort): {x = y} + {x ≠ y}.
  Proof.
    decide equality.
  Defined.
x
  Function lookup (x: string) (Γ: env): option sort :=
    match Γ with

    | (y, τ) :: T => if string_dec x y then Some τ else lookup x T
    | _ => None
    end.

  Function infer (Γ: env) (e: term): option sort :=
    match e with
    | var x => lookup x Γ
    | lam x τ0 e =>
      if infer ((x, τ0)::Γ) e is Some τ1
      then
        Some (exp τ0 τ1)
      else
        None
    | app e0 e1 =>
      if infer Γ e0 is Some (exp τ0 τ1)
      then
        if infer Γ e1 is Some τ0'
        then
          if sort_dec τ0 τ0'
          then
            Some τ1
          else
            None
        else
          None
      else
        None
    end.

  Definition sound {Γ e τ}:
    infer Γ e = Some τ →
    theorem [] [Γ ⊢ e ∈ τ].
  Proof.
    generalize dependent τ.
    functional induction (infer Γ e).
    all: intros τ p.
    all: inversion p.
    all: subst.
    2: {
      refine (lam' Γ x τ0 τ1 e0 ∘ _).
      apply IHo.
      auto.
    }
    2: {
      refine (app' Γ e0 e1 τ0 τ ∘ _).
      cbn.
      
    induction e.
    all: intros Γ A p.
    all: cbn in *.
    all: inversion p.
    all: subst.
    - Check (IHe ((x, τ) :: Γ) A p).
      all: subst.
      + cbn.
End Stlc.

Module Import Finite.
  Fixpoint fin (n: nat) :=
    match n with
    | O => Empty_set
    | S n' => option (fin n')
    end.

  Definition swap N (x: fin (2 + N)): fin (2 + N) :=
    match x with
    | Some (Some e) => Some (Some e)
    | Some None => None
    | None => Some None
    end.

  Definition weaken N (x: fin N): fin (S N) := Some x.

  Definition contract N (x: fin (2 + N)): fin (S N) :=
    match x with
    | Some (Some e) => Some e
    | Some None => None
    | None => None
    end.

  (* Not really sure about this *)
  Definition fold N (x: fin (N + N)): fin N.
  Proof.
    induction N.
    - cbn in *.
      contradiction.
    - cbn in *.
      rewrite Nat.add_comm in x.
      cbn in *.
      refine (match x with
              | Some (Some x') => Some (IHN x')
              | _ => None
              end).
  Defined.

End Finite.

(* Free category on an endospan/free monad in Span(Set) *)
Module Cat.
  Import Span.

  (* Doesn't seem right *)
  #[universes(cumulative)]
   Inductive free {Obj} (H: span Obj Obj): Obj → Obj → Type :=
  | id A: free H A A
  | compose {A B C}: free H B C → free H A B → free H A C
  | sup x: free H (π1 H x) (π2 H x)
  .
  Arguments id {Obj H}.
  Arguments compose {Obj H A B C}.
  Arguments sup {Obj}.
End Cat.

(* Free indexed category on a displayed category *)
Module IxCat.
  Import Span.
  Import Cat.

  Record displayed C := {
    op: C → Type ;
    map (c: C): span (op c) (op c) ;
  }.

  Arguments op {C}.
  Arguments map {C}.

  Coercion op: displayed >-> Funclass.

  (* A displayed category C -> Span defines a functor D -> C *)

  Definition free {V} (H: displayed V) Γ := free (map H Γ).
End IxCat.

Module CylCat.
  Import Span.
  Import Cat.
  Import IxCat.

  Definition displayed V := displayed (string → V).

  (* A cylindrified displayed category [string, V] -> Span defines an
  indexed category [string, V] → Cat *)
  Definition free {V} (H: displayed V) Γ := free H Γ.
End CylCat.



(* Free indexed monad on an indexed polynomial endofunctor *)
Module IxPoly.
   #[universes(cumulative)]
   Record Poly Env := {
    pos: Type ;
    dir: pos → Env → Type ;
  }.

   Arguments pos {Env}.
   Arguments dir {Env}.

   Definition X Γ: Poly Γ := {|
     dir (_: unit) _ := unit ;
   |}.
  (* Definition K A: Poly := {| dir (_: A) := Empty_set |}. *)

  (* Definition Π {A} (p: A → Poly): Poly := *)
  (*   {| *)
  (*   pos := ∀ i, pos (p i) ; *)
  (*   dir s := Σ i, dir (p i) (s i) ; *)
  (*   |}. *)
  (* Definition Sum {A} (p: A → Poly): Poly := *)
  (*   {| *)
  (*   pos := Σ i, pos (p i) ; *)
  (*   dir s := dir (p (head s)) (tail s) ; *)
  (*   |}. *)

  (* Definition prod (p q: Poly): Poly := *)
  (*   {| *)
  (*   pos := pos p * pos q ; *)
  (*   dir '(x, y) := dir p x + dir q y ; *)
  (*   |}. *)

  (* Definition sum (p q: Poly): Poly := *)
  (*   {| *)
  (*   pos := pos p + pos q ; *)
  (*   dir s := *)
  (*     match s with *)
  (*     | inl x' => dir p x' *)
  (*     | inr x' => dir q x' *)
  (*     end ; *)
  (*   |}. *)

  (* Infix "*" := prod. *)
  (* Infix "+" := sum. *)

  #[universes(cumulative)]
  Inductive free {Env} (H: Poly Env) A: Env → Type :=
  | var {Γ}: A Γ → free H A Γ
  | sup {Γ} x: (dir H x Γ → free H A Γ) → free H A Γ.
  Arguments var {Env H A Γ}.
  Arguments sup {Env H A Γ}.

  Definition map {Env} {H: Poly Env} {A B} (f: ∀ Γ, A Γ → B Γ): ∀ {Γ}, free H A Γ → free H B Γ :=
    fix loop Γ x :=
      match x with
      | var v => var (f _ v)
      | sup x p => sup x (fun y => loop _ (p y))
      end.
  Definition join {Env} {H: Poly Env} {A}: ∀ {Γ}, free H (free H A) Γ → free H A Γ :=
    fix loop Γ x :=
      match x with
      | var v => v
      | sup x p => sup x (fun y => loop _ (p y))
      end.
End IxPoly.

(* Free indexed category on an indexed endospan/free indexed monad in Span(Set) *)
  Record bundle B := {
    dom: Type ;
    π: dom → B;
  }.
  Arguments dom {B}.
  Arguments π {B}.
  Coercion dom: bundle >-> Sortclass.

  #[universes(cumulative)]
   Record span {Env} (A B: bundle Env) := {
    s: Type ;
    π1: s → A ;
    π2: s → B ;
  }.

  Arguments s {Env A B}.
  Arguments π1 {Env A B}.
  Arguments π2 {Env A B}.

  Coercion s: span >-> Sortclass.

  #[universes(cumulative)]
   Inductive free {Env} {Obj: bundle Env} (H: span Obj Obj): Env → Obj → Obj → Type :=
  | id {Γ} A: free H Γ A A
  | compose {Γ} {A B C}: free H Γ B C → free H Γ A B → free H Γ A C

  | sup x: (π Obj (π1 H x) = π Obj (π2 H x)) →
            free H (π Obj (π1 H x)) (π1 H x) (π2 H x)
  .
  Arguments id {Env Obj H Γ}.
  Arguments compose {Env Obj H Γ A B C}.
  Arguments sup {Env Obj}.
End IxCat.
