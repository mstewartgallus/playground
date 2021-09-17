
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
Require Import Coq.Vectors.VectorDef.
Require Coq.Vectors.Fin.

Import IfNotations.
Import ListNotations.

#[universes(cumulative)]
Record vec N := {
  pos: Type;
  dir: pos → N ;
}.
Arguments pos {N}.
Arguments dir {N}.

Definition K {N} (c: Type): vec N := {| dir (xy: c * N) := snd xy ; |}.

Inductive fiber {N} (v: vec N): N → Type :=
| sup ii: fiber v (dir v ii).

Infix "!" := fiber (at level 30).

#[universes(cumulative)]
Record mat M N := {
  val: Type ;
  i: val → M ;
  j: val → N ;
}.
Arguments val {M N}.
Arguments i {M N}.
Arguments j {M N}.

Definition outer {A} (f: vec A) (g: vec A): mat A A :=
  {|
  val := pos f * pos g ;
  i '(x, y) := dir f x ;
  j '(x, y) := dir g y ;
 |}.
Infix "⊗" := outer (at level 30).

Definition I N: mat N N := {|
  val := { '(x, y) | x = y } ;
  i xy := fst (proj1_sig xy) ;
  j xy := snd (proj1_sig xy) ;
|}.

Definition compose {A B C} (f: mat B C) (g: mat A B): mat A C :=
  {|
  val := { '(x, y) | i f x = j g y } ;
  i xy := i g (snd (proj1_sig xy)) ;
  j xy := j f (fst (proj1_sig xy)) ;
  |}.
Infix "∘" := compose (at level 30).

Definition kronecker {A B C D} (f: mat A B) (g: mat C D): mat (A * C) (B * D) :=
  {|
  val := val f * val g ;
  i '(x, y) := (i f x, i g y) ;
  j '(x, y) := (j f x, j g y) ;
 |}.
Infix "×" := kronecker (at level 30).

Definition trace {A} (f: mat A A) := { x | i f x = j f x }.

Definition inner {A} (f: vec A) (g: vec A) := trace (f ⊗ g).
Infix "·" := inner (at level 30).

Fixpoint sum (l: list Type): Type :=
  match l with
  | [] => Empty_set
  | H :: T => H + sum T
  end.

Definition oflist (l: list Type): sum l → Fin.t (length l).
Proof.
  induction l.
  - cbn.
    contradiction.
  - cbn.
    intros [x|y].
    + constructor.
    + apply Fin.FS.
      apply IHl.
      apply y.
Defined.

Definition mkvec (l: list Type): vec (Fin.t (length l)) := {| dir := oflist l |}.

#[program]
Definition foo: mkvec [ bool ; unit ; unit ] · mkvec [ nat ; unit ; unit ] := (inl false, inl 0).
