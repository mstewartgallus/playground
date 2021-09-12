#[global]
Set Primitive Projections.
#[global]
Unset Printing Primitive Projection Parameters.

#[global]
Set Universe Polymorphism.

#[global]
Set Default Goal Selector "!".

Require Import Coq.Unicode.Utf8.
Require Import Coq.Program.Tactics.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Import IfNotations.
Import ListNotations.

#[universes(cumulative)]
Record span A B := {
  s: Type ;
  π1: s → A ;
  π2: s → B ;
}.
Arguments s {A B}.
Arguments π1 {A B}.
Arguments π2 {A B}.

Definition id A: span A A :=
  {|
  s := A ;
  π1 x := x ;
  π2 x := x ;
  |}.

Definition compose {A B C} (f: span B C) (g: span A B): span A C :=
  {|
  s := { xy | π1 f (fst xy) = π2 g (snd xy) } ;
  π1 xy := π1 g (snd (proj1_sig xy)) ;
  π2 xy := π2 f (fst (proj1_sig xy)) ;
  |}.
Infix "∘" := compose (at level 30).

Inductive ext {A B} (F: span A B): A → B → Type :=
| sup (x: s F): ext F (π1 F x) (π2 F x).

Definition tag {A B} {F: span A B} {C D} (e: ext F C D) :=
  let '(sup _ x) := e in
  x.

(* dependent product basically

 should be like Ran P Q A B = forall x, P(x, A) → Q(x, B)

  x <- P -> A
  ———-
  x <- Q -> B
 *)
Record Ran {C D E} (F: span C D) (G: span C E) := {
  x: D ;
  y: E ;
  p A: ext F A x → ext G A y ;
}.
Arguments x {C D E F G}.
Arguments y {C D E F G}.

Arguments p {C D E F G}.

#[program]
Definition ran {C D E} (F: span C D) (G: span C E): span D E :=
  {|
  s := Ran F G ;
  π1 r := x r ;
  π2 r := y r ;
  |}.
Notation "[ A , B ]" := (ran A B).

Definition codensity {A B} (F: span A B) := [F, F].

Definition codensity_id {A B} (F: span A B) (x: B): ext (codensity F) x x.
Proof.
  cbn in *.
  refine (sup (codensity F) {| x := x ; y := x |}).
  intros.
  apply X.
Defined.

Definition codensity_compose {K L} {F: span K L} {A B C}: ext (codensity F) B C → ext (codensity F) A B → ext (codensity F) A C.
Proof.
  intros f g.
  destruct f as [f].
  cbn in *.
  (* A little odd finagling here is required *)
  remember (x f) as B'.
  destruct g as [g].
  cbn in *.
  refine (sup (codensity F) {| x := x g ; y := y f |}).
  intros.
  apply (p f).
  rewrite <- HeqB'.
  apply (p g).
  auto.
Defined.

Definition eval {A B} (F: span A B) (G: span A B): s ([ F , G ] ∘ F) → s G.
Proof.
  cbn in *.
  intros [[[?] ?] ?].
  cbn in *.
  refine (tag (p0 _ _)).
  Unshelve.
  2: {
    apply (π1 F s0).
  }
  subst.
  apply (sup F s0).
Defined.

(* Garbage prototype *)

Inductive term :=
| var (x: string)
| lam (x: string) (e: term)
| app (e0 e1: term).

Inductive rule :=
| var_rule (n: nat) (x: string)
| lam_rule (n: nat) (x: string) (e: term)
| app_rule (n: nat) (e0 e1: term)
.

Definition vars (r: rule): nat * term :=
  match r with
  | var_rule n x => (S n, var x)
  | lam_rule n x e => (n, lam x e)
  | app_rule n e0 e1 => (n, app e0 e1)
  end.

Definition Vars := {| π1 x := fst (vars x) ; π2 x := snd (vars x) |}.

Definition VARS := ext (codensity Vars).

Definition VARS_id: ∀ x, VARS x x := codensity_id Vars.
Definition VARS_compose {A B C}: VARS B C → VARS A B → VARS A C := @codensity_compose _ _ Vars _ _ _.

Definition VARS_rule {x y} (p: ∀ A, ext Vars A x → ext Vars A y): VARS _ _ := sup (codensity Vars) {| p := p |}.

