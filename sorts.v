#[global]
Set Primitive Projections.
#[global]
Unset Printing Primitive Projection Parameters.

#[global]
Set Universe Polymorphism.

#[global]
Set Default Goal Selector "!".

Require Import Coq.Unicode.Utf8.

Import IfNotations.

Inductive Tag := Const | Sum | Prod.
Definition eq_Tag (x y: Tag): {x = y} + {x ≠ y}.
Proof.
  decide equality.
Defined.

Definition eqb x y := if eq_Tag x y then True else False.

#[universes(cumulative)]
CoInductive U := u {
  tag: Tag ;
  const_u: eqb tag Const → Type ;
  sum_left: eqb tag Sum → U ;
  sum_right: eqb tag Sum → U ;
  prod_left: eqb tag Prod → U ;
  prod_right: eqb tag Prod → U ;
}.

Notation "'const' A" := {|
  tag := Const ;
  const_u _ := A ;

  prod_left x := match x: False with end ;
  prod_right x := match x: False with end ;
  sum_left x := match x: False with end ;
  sum_right x := match x: False with end ;
|} (at level 1).

Notation "A * B" := {|
  tag := Prod ;
  prod_left _ := A ;
  prod_right _ := B ;

  const_u x := match x: False with end ;
  sum_left x := match x: False with end ;
  sum_right x := match x: False with end ;
|}.
Notation "A + B" := {|
  tag := Sum ;
  sum_left _ := A ;
  sum_right _ := B ;

  const_u x := match x: False with end ;
  prod_left x := match x: False with end ;
  prod_right x := match x: False with end ;
|}.

Definition is_const: U → option Type.
Proof.
  intro u.
  destruct u.
  destruct (eq_Tag tag0 Const).
  2: apply None.
  subst.
  apply Some.
  apply const_u0.
  apply I.
Defined.

Definition is_sum: U → option (U * U).
Proof.
  intro u.
  destruct u.
  destruct (eq_Tag tag0 Sum).
  2: apply None.
  subst.
  apply Some.
  split.
  - apply sum_left0.
    cbn.
    apply I.
  - apply sum_right0.
    cbn.
    apply I.
Defined.

Definition is_prod: U → option (U * U).
Proof.
  intro u.
  destruct u.
  destruct (eq_Tag tag0 Prod).
  2: apply None.
  subst.
  apply Some.
  split.
  - apply prod_left0.
    cbn.
    apply I.
  - apply prod_right0.
    cbn.
    apply I.
Defined.

#[universes(cumulative)]
Inductive El (u: U) :=
| El_const:
    (if is_const u is Some T then T else False) → El u
| El_pair:
    El (if is_prod u is Some (A, _) then A else const Empty_set) →
    El (if is_prod u is Some (_, B) then B else const Empty_set) →
    El u
| El_inl:
    El (if is_sum u is Some (A, _) then A else const Empty_set) →
    El u
| El_inr:
    El (if is_sum u is Some (_, B) then B else const Empty_set) →
    El u
.

Coercion El: U >-> Sortclass.

Definition pt: El (const unit) := El_const (const unit) tt.

CoFixpoint list A := const unit + (const A * list A).

Definition nil {A}: list A := El_inl (list A) (El_const (const unit) tt).
Definition cons {A} (h: A) (t: list A): list A :=
  El_inr (list A) (El_pair (const A * list A) (El_const (const A) h) t).
