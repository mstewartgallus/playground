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

  Definition V x: Poly := {| dir (_: unit) y := x = y |}.
  Definition K A: Poly := {| dir (_: A) _ := Empty_set |}.

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

  Definition subst (x: string) (A: Type) Γ := λ y, if string_dec x y then A else Γ y.

  Definition Π {A} (p: A → Poly): Poly :=
    {|
    pos := ∀ i, pos (p i) ;
    dir s x := someT (fun i => dir (p i) (s i) x) ;
    |}.
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

  Definition scope (x: string) (A: Type) (Γ: string → Type) := λ y, {_: A | x = y } + { _: Γ y | x ≠ y }.

  Infix "*" := prod.
  Infix "+" := sum.

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

  Open Scope nat_scope.
  Example bar := poflist [1 ; 3 ; 5].
End CylPoly.

(* Free monad on a polynomial endofunctor *)
Module Poly.
  #[universes(cumulative)]
   Record Poly := {
    pos: Type ;
    dir: pos → Type ;
  }.

  Coercion pos: Poly >-> Sortclass.

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

  Definition K A: Poly := {| dir (_: A) := Empty_set |}.

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

  Class Span_Mor {A B} {s: span A B} {t: span A B} (f: s → t) := {
    map_π1 x: π1 t (f x) = π1 s x ;
    map_π2 x: π2 t (f x) = π2 s x ;
  }.
End Span.

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

Definition Fin (xs: list string) := fin (List.length xs).

Record Arena := {
  pos: Type ;
  dir: pos → nat ;
}.

Record ext (P: Arena) A :=
  sup {
      tag: _ ;
      field: fin (dir P tag) → A ;
    }.

Arguments sup {P A}.
Arguments tag {P A}.
Arguments field {P A}.

Infix "!" := field (at level 30).

Coercion ext: Arena >-> Funclass.

Open Scope nat_scope.

(* Seems awkward, but sounds kind of right *)
Definition Sum {A} (p: fin A → nat): nat.
Proof.
  induction A.
  - apply 0.
  - apply (IHA (λ x, p (Some x)) + p None).
Defined.

Lemma S_Proper: Proper (eq ==> eq) S.
Proof.
  intros ? ? p.
  subst.
  reflexivity.
Qed.

Lemma Sum_1 {N}: Sum (λ _ : fin N, 1) = N.
Proof.
Admitted.

Definition Π {A} (p: fin A → Arena): Arena :=
{|
  pos := ∀ i, pos (p i) ;
  dir s := Sum (fun i => dir (p i) (s i)) ;
|}.

Definition compose (p q: Arena): Arena :=
{|
  pos := p (pos q) ;
  dir x :=
    (* Product or sum ? *)
    Sum (fun fld => dir q (x ! fld)) ;
|}.

Infix "∘" := compose (at level 30).

Definition Σ {A} (p: A → Arena): Arena :=
{|
  pos := someT (fun i => pos (p i)) ;
  dir s := dir (p (head s)) (tail s) ;
|}.

Definition K (s: Type) : Arena := {|
  pos := s ;
  dir _ := 0 ;
|}.

Definition prod (p q: Arena): Arena :=
{|
  pos := pos p * pos q ;
  dir '(x, y) := dir p x + dir q y ;
|}.

Definition sum (p q: Arena): Arena :=
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

Definition X: Arena := {|
    pos := unit ;
    dir _ := 1 ;
|}.

Definition δ: Arena := K unit + X.

Definition D (p: Arena): Arena := p ∘ δ.

Record Mor (A B: Arena) := {
  op: pos A → pos B ;
  map x: fin (dir B (op x)) → fin (dir A x) ;
}.

Arguments op {A B}.
Arguments map {A B}.

(* #[program] *)
(* Definition swap {A: Arena}: Mor (δ ∘ δ) (δ ∘ δ) := *)
(* {| *)
(*   op p := p ; *)
(*   map x y := _ ; *)
(* |}. *)


#[program]
Definition up {A: Arena}: Mor X δ := {|
  op _ := inr tt ;
|}.

#[program]
Definition contract {A: Arena}: Mor (δ ∘ δ) δ :=
  {|
  op p := _ ;
  map x y := _ ;
  |}.

Next Obligation.
Proof.
  destruct p.
  cbn in *.
  destruct tag0.
  - apply (inl tt).
  - cbn in *.
    apply (field0 None).
Defined.

Next Obligation.
Proof.
  unfold contract_obligation_1 in *.
  cbn in *.
  destruct x.
  cbn in *.
(* #[program] *)
(*  Definition eval {A: Arena} {x}: Mor (V x * D x A) A := *)
(*   {| *)
(*   op p := _ ; *)
(*   map x y := _ ; *)
(*   |}. *)

(* Next Obligation. *)
(* Proof. *)
(*   apply (tag e). *)
(* Defined. *)

(* Next Obligation. *)
(* Proof. *)
(*   cbn in *. *)
(*   refine (Some _). *)
(* Defined. *)



(* Free category on an endospan/free monad in Span(Set) *)
Module Cat.
  Import Span.

  #[universes(cumulative)]
   Inductive free {Obj} (H: span Obj Obj): Obj → Obj → Type :=
  | id A: free H A A
  | compose {A B C}: free H B C → free H A B → free H A C
  | sup x: free H (π1 H x) (π2 H x)
  .
  Arguments id {Obj H}.
  Arguments compose {Obj H A B C}.
  Arguments sup {Obj}.

  Definition Free {Obj} (H: span Obj Obj): span Obj Obj := {|
    s := (Σ x y, free H x y) ;
    π1 xy := head xy ;
    π2 xy := head (tail xy) ;
  |}.

  Definition Sup {Obj} (H: span Obj Obj) (x: H): Free H.
    exists (π1 H x).
    exists (π2 H x).
    apply (sup H x).
  Defined.
End Cat.

(* Free indexed category on a displayed category *)
Module IxCat.
  Import Span.

  Record displayed C := {
    op: C → Type ;
    map (c: C): span (op c) (op c) ;
  }.

  Arguments op {C}.
  Arguments map {C}.

  (* A displayed category C -> Span defines a functor D -> C *)

  (* Kind of like a comma category *)
  Record bundle {C} (H: displayed C) (c: C) := {
    s: span (op H c) (op H c) ;
    π: s → map H c ;
    π_Span_Mor:> Span_Mor π ;
  }.
  Arguments s {C H c}.
  Arguments π {C H c}.
  Coercion s: bundle >-> span.

  Definition over {C} (H: displayed C) c (s t: bundle H c) :=
    { f: s → t | Span_Mor f ∧ ∀ x, π s x = π t (f x) }.
End IxCat.

Module Stlc.
  Import Cat.
  Import IxCat.
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

  Inductive rule: env → sort → Type :=
  | var_rule (Γ: env) (x: string) (τ: sort) (p: In (x, τ) Γ): rule Γ τ
  | lam_rule (Γ: env) (x: string) (τ0 τ1: sort) (e:term): rule Γ (exp τ0 τ1)
  | app_rule (Γ: env) (e0 e1: term) (τ0 τ1: sort): rule Γ τ1
  .

  Example judge (Γ: env) (τ: sort) (r: rule Γ τ): (list fact * list fact) :=
    match r with
    | var_rule Γ x τ _ =>
      ([],
       [Γ ⊢ var x ∈ τ])
    | lam_rule Γ x τ0 τ1 e =>
      ([((x, τ0) :: Γ) ⊢ e ∈ τ1],
       [Γ ⊢ lam x τ0 e ∈ exp τ0 τ1])
    | app_rule Γ e0 e1 τ0 τ1 =>
      ([Γ ⊢ e0 ∈ exp τ0 τ1 ; Γ ⊢ e1 ∈ τ0],
       [Γ ⊢ app e0 e1 ∈ τ1])
    end.

  Example theory := {|
    map e := {|
              π1 r := fst (judge (fst e) (snd e) r) ;
              π2 r := snd (judge (fst e) (snd e) r) ;
            |} ;
  |}.
  Definition theorem {c} := over theory c.

  Definition bun Γ τ
             (s: span (op theory (Γ, τ)) (op theory (Γ, τ)))
             (f: s → map theory (Γ, τ))
    `{Span_Mor _ _ _ _ f}: bundle theory (Γ, τ).
    exists s f.
    auto.
  Defined.

  Instance id_Span_Mor Γ τ: Span_Mor (λ x : map theory (Γ, τ), x).
  Proof.
    exists.
    - cbn.
      intro.
      reflexivity.
    - cbn.
      intro.
      reflexivity.
  Qed.

  Definition ident Γ τ := bun Γ τ (λ x, x).

  Definition foo Γ τ: theorem (ident Γ τ) (ident Γ τ).
  Proof.
    eexists.
    Unshelve.
    2: {
      auto.
    }
  Admitted.

  (* A -> m A *)
  (* kleisli arrow ~ pure ~ id
    O -> span O O

    based around join/map
   A * (A -> m b) -> m b
   *)

  (* Inductive ext {Obj} (S: span Obj Obj): Obj → Obj → Type := *)
  (* | ext_intro x: ext S (π1 S x) (π2 S x). *)

  (* Definition codensity A := ∀ B C, (A → ext theory B C) → ext theory B C. *)

(* Codensity monad

 *)

  Example var' Γ x τ p: theorem (Γ ⊢ var x ∈ τ) [] [Γ ⊢ var x ∈ τ] := sup (map theory _) (var_rule Γ x τ p).

  Example lam' Γ x τ0 τ1 e: free theory _ [_] [_] := sup (map theory _) (lam_rule Γ x τ0 τ1 e).

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
