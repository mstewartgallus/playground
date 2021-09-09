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

#[universes(cumulative)]
CoInductive U :=
| const (T: Type)
| sum (_ _: U)
| prod (_ _: U)
.

Infix "*" := prod.
Infix "+" := sum.

Definition leftu (u: U): U :=
  match u with
  | sum l _ => l
  | _ => const Empty_set
  end.
Definition rightu (u: U): U :=
  match u with
  | sum _ r => r
  | _ => const Empty_set
  end.

Definition cast {u} (x: if u is _ + _ then bool else unit): option bool.
Proof.
  destruct u.
  - apply None.
  - apply Some.
    apply x.
  - apply None.
Defined.

#[universes(cumulative)]
CoInductive El (u: U) := el {
  unbox: if u is const T then T else unit ;

  fst: El (if u is A * _ then A else const unit) ;
  snd: El (if u is _ * B then B else const unit) ;

  tag:
    if u is _ + _ then bool else unit ;
  left:
    El (if cast tag is Some false then leftu u else const unit) ;
  right:
    El (if cast tag is Some true then rightu u else const unit) ;
}.

Arguments unbox {u}.
Arguments fst {u}.
Arguments snd {u}.
Arguments tag {u}.
Arguments left {u}.
Arguments right {u}.

Coercion El: U >-> Sortclass.

Definition pt: const unit.
Proof.
  cofix p.
  econstructor.
  Unshelve.
  6: apply tt.
  - apply tt.
  - apply p.
  - apply p.
  - cbn.
    apply p.
  - cbn.
    apply p.
Defined.

Notation "'box' x" := (el (const _) x pt pt tt pt pt) (at level 1).
Notation "⟨ x , y ⟩" := (el (prod _ _) tt x y tt pt pt).
Notation "'inl' x" := (el (sum _ _) tt pt pt false x pt) (at level 1).
Notation "'inr' x" := (el (sum _ _) tt pt pt true pt x) (at level 1).

Definition foo {A} (x: A): const A := box x.
Definition bar {A B} (x: El A) (y: El B): El (A * B) := ⟨ x , y ⟩.
Definition l {A B} (x: El A): El (A + B) := inl x.
Definition r {A B} (x: El B): El (A + B) := inr x.

CoFixpoint list A := const unit + (const A * list A).

Definition nil {A}: list A.
  unfold list.
  cbn in *.
  econstructor.
  Unshelve.
  all: cbn in *.
  6: apply false.
  all: cbn in *.
  all: try apply pt.
Defined.

Definition cons {A} (h: A) (t: list A): list A.
  unfold list.
  cbn in *.
  econstructor.
  Unshelve.
  all: cbn in *.
  6: apply true.
  all: cbn in *.
  all: try apply pt.
  refine ⟨ _, _ ⟩.
  - apply (box h).
  - apply t.
Defined.
