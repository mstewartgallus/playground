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
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Psatz.
Require Import Recdef.

Import IfNotations.
Import ListNotations.

Close Scope nat.

Definition valof {C} (P: C → bool) y := {
  val: C | Is_true (implb (P val) y) }.

#[program]
Definition app {C} (P: C → bool) (x: valof P false): valof P true := x.

Next Obligation.
Proof.
  destruct (P (proj1_sig x)).
  - cbn.
    apply I.
  - cbn.
    apply I.
Defined.

Record fiber {C} (P: C → bool) y := {
  tag: valof P true ;
  field: { x: valof P false | proj1_sig (app P x) = proj1_sig tag } → y ;
}.

Arguments tag {C P y}.
Arguments field {C P y}.

Record Poly := {
  pos: Type ;
  dir: pos → bool ;
}.

Definition X := {| dir (_: unit) := false |}.

Definition K A := {| dir (_: A) := true |}.

Definition sum (P Q: Poly) :=
  {|
  dir (x: pos P + pos Q) :=
    match x with
    | inl x' => dir P x'
    | inr x' => dir Q x'
    end ;
  |}.

Definition K_in {A B} (x: A): fiber (dir (K A)) B.
Proof.
  cbn.
  eexists (exist _ x _).
  Unshelve.
  2: {
    cbn.
    apply I.
  }
  intros [[?] ?].
  cbn in *.
  contradiction.
Defined.

Definition K_out {A B}: fiber (dir (K A)) B → A.
Proof.
  intros [a ?].
  cbn in *.
  apply a.
Defined.

Definition X_in {A} (x: A): fiber (dir X) A.
Proof.
  cbn.
  eexists (exist _ tt _).
  Unshelve.
  2: {
    cbn.
    apply I.
  }
  intro.
  apply x.
Defined.

Definition X_out {A}: fiber (dir X) A → A.
Proof.
  intros [? p].
  cbn in *.
  apply p.
  eexists (exist _ tt _).
  Unshelve.
  2: {
    cbn.
    apply I.
  }
  cbn.
  destruct tag0.
  cbn.
  destruct x.
  reflexivity.
Defined.

Definition inl_intro {A B C}: fiber (dir A) C → fiber (dir (sum A B)) C.
Proof.
  intros [[a j] p].
  cbn in *.
  exists (exist _ (inl a) j).
  cbn.
  intros [[? ?] ?].
  cbn in *.
  subst.
  apply p.
  eexists.
  Unshelve.
  2: {
    exists a.
    apply i.
  }
  cbn.
  reflexivity.
Defined.

Definition inr_intro {A B C}: fiber (dir B) C → fiber (dir (sum A B)) C.
Proof.
  intros [[b j] p].
  cbn in *.
  exists (exist _ (inr b) j).
  cbn.
  intros [[? ?] ?].
  cbn in *.
  subst.
  apply p.
  eexists.
  Unshelve.
  2: {
    exists b.
    apply i.
  }
  cbn.
  reflexivity.
Defined.

Definition sum_out {A B C}: fiber (dir (sum A B)) C → fiber (dir A) C + fiber (dir B) C.
Proof.
  intros [[[a|b] i] p].
  all: cbn in *.
  - left.
    exists (exist _ a i).
    intros [[? j] ?].
    cbn in *.
    subst.
    apply p.
    exists (exist _ (inl a) j).
    cbn.
    reflexivity.
  - right.
    exists (exist _ b i).
    intros [[? j] ?].
    cbn in *.
    subst.
    apply p.
    exists (exist _ (inr b) j).
    cbn.
    reflexivity.
Defined.

(* How bizarre it's a kind of pullback *)
Definition prod (P Q: Poly) :=
  {|
  dir (x: pos P * pos Q) := eqb (dir P (fst x)) (dir Q (snd x)) ;
  |}.

Definition prod_intro {A B C}: fiber (dir A) C → fiber (dir B) C → fiber (dir (prod A B)) C.
Proof.
  intros [[a j] p] [[b k] q].
  eexists (exist _ (a, b) _).
  Unshelve.
  2: {
    cbn in *.
    destruct (dir A a) eqn:r, (dir B b) eqn:s.
    all: cbn in *.
    all: apply I.
  }
  intros [[[? ?] ?] ?].
  cbn in *.
  inversion e.
  subst.
  destruct (dir A a) eqn:r, (dir B b) eqn:s.
  all: cbn in *.
  - contradiction.
  - apply q.
    eexists (exist _ b _).
    Unshelve.
    2: {
      cbn.
      rewrite s.
      cbn.
      apply I.
    }
    cbn.
    reflexivity.
  - apply p.
    eexists (exist _ a _).
    Unshelve.
    2: {
      cbn.
      rewrite r.
      cbn.
      apply I.
    }
    cbn.
    reflexivity.
  - contradiction.
Defined.
