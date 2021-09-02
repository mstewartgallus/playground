#[global]
Set Primitive Projections.
#[global]
Unset Printing Primitive Projection Parameters.

#[global]
Set Universe Polymorphism.

#[global]
Set Default Goal Selector "!".

Require Import Coq.Unicode.Utf8.
Require Import Coq.Strings.String.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.PeanoNat.
Require Import FunInd.

Import IfNotations.

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
End SomeNotations.

Inductive U := set | type (n: nat).

Definition U_dec (x y: U): {x = y} + { x ≠ y}.
Proof.
  set (s := Nat.eq_dec).
  decide equality.
Defined.

Definition succU u :=
  match u with
  | set => type 0
  | type n => type (n + 1)
  end.

Inductive term :=
| ofU (u: U)

| all (x: string) (e0 e1: term)

| var (x: string)
| lam (x: string) (e0 e1: term)
| app (e0 e1: term)

| compose (e0 e1: term)
| sym (e: term)

| beta (x: string) (A e0 e1: term)
.

Infix "∘" := compose (at level 30).

Coercion ofU: U >-> term.
Coercion var: string >-> term.

Definition term_dec (x y: term): {x = y} + { x ≠ y}.
Proof.
  set (u := U_dec).
  set (s := string_dec).
  decide equality.
Defined.

Definition mt: string → term := var.
Definition put x A (Γ: string → term) : string → term :=
  λ y, if string_dec x y then A else Γ y.

Inductive
  substs (x: string) (s: term): term → term → Type :=
| substs_ofU u: substs x s (ofU u) (ofU u)

| substs_var_eq: substs x s (var x) s
| substs_var_ne y: x ≠ y → substs x s (var y) (var y)

| substs_all_eq A A' e:
    substs x s A A' →
    substs x s (all x A e) (all x A' e)
| substs_all_ne y A A' e e':
    x ≠ y →
    substs x s A A' →
    substs x s e e' →
    substs x s (all y A e) (all y A' e')

| substs_lam_eq A A' e:
    substs x s A A' →
    substs x s (lam x A e) (lam x A' e)
| substs_lam_ne y A A' e e':
    x ≠ y →
    substs x s A A' →
    substs x s e e' →
    substs x s (lam y A e) (lam y A' e')

| substs_app e0 e1 e0' e1':
    substs x s e0 e0' →
    substs x s e1 e1' →
    substs x s (app e0 e1) (app e0' e1')

| substs_compose e0 e1 e0' e1':
    substs x s e0 e0' →
    substs x s e1 e1' →
    substs x s (e0 ∘ e1) (e0' ∘ e1')
| substs_sym e0 e0':
    substs x s e0 e0' →
    substs x s (sym e0) (sym e0')

| substs_beta_eq A A' e0 e1 e1':
    substs x s A A' →
    substs x s e1 e1' →
    substs x s (beta x A e0 e1) (beta x A' e0 e1')
| substs_beta_ne y A A' e0 e0' e1 e1':
    x ≠ y →
    substs x s A A' →
    substs x s e0 e0' →
    substs x s e1 e1' →
    substs x s (beta y A e0 e1) (beta y A' e0' e1')
.

Function subst x s t :=
  match t with
  | ofU u => ofU u

  | all y A e => if string_dec x y then all y (subst x s A) e else all y (subst x s A) (subst x s e)

  | var y => if string_dec x y then s else t
  | lam y A e => if string_dec x y then lam y (subst x s A) e else lam y (subst x s A) (subst x s e)
  | app e0 e1 => app (subst x s e0) (subst x s e1)

  | e0 ∘ e1 => subst x s e0 ∘ subst x s e1
  | sym e => sym (subst x s e)
  | beta y A f e => if string_dec x y then beta y (subst x s A) f (subst x s e) else beta y (subst x s A) (subst x s f) (subst x s e)
  end.
Notation "[ x := e0 ]" := (subst x e0).

Definition subst_sound:
  ∀ {x s e e'},
  e' = [x := s] e →
  substs x s e e'.
Proof.
  intros x s e.
  functional induction ([x := s] e).
  all: intros e' p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: try eauto.
Defined.

Definition subst_complete:
  ∀ {x s e e'},
  substs x s e e' →
  e' = [x := s] e.
Proof.
  intros x s e.
  induction e.
  all: intros e' p.
  all: inversion p.
  all: subst.
  all: cbn in *.
  all: repeat rewrite (IHe1 _ H3).
  all: repeat rewrite (IHe1 _ H4).
  all: repeat rewrite (IHe1 _ H5).
  all: repeat rewrite (IHe3 _ H5).
  all: repeat rewrite (IHe2 _ H6).
  all: repeat rewrite (IHe3 _ H7).
  all: repeat rewrite (IHe _ H0).
  all: repeat rewrite (IHe1 _ H1).
  all: repeat rewrite (IHe2 _ H3).
  all: repeat rewrite (IHe2 _ H5).
  all: try reflexivity.
  all: try destruct (string_dec x0 x0).
  all: try contradiction.
  all: try reflexivity.
  all: try destruct (string_dec x x0).
  all: try contradiction.
  all: try reflexivity.
Defined.


Reserved Notation "x ; A ≡ B" (at level 80).

Inductive
  maps: term → term → term → Type :=

| maps_ofU u:
    ofU u ; ofU u ≡ ofU u
| maps_var x:
    var x ; var x ≡ var x

| maps_all x A e p q r s:
    A ; p ≡ q →
    e ; r ≡ s →
    all x A e ; all x p r ≡ all x q s

| maps_lam x A e p q r s:
    A ; p ≡ q →
    e ; r ≡ s →
    lam x A e ; lam x p r ≡ lam x q s

| maps_app e0 e1 p q r s:
    e0 ; p ≡ q →
    e1 ; r ≡ s →
    app e0 e1 ; app p r ≡ app q s

| maps_compose e0 e1 p q r:
    e0 ; q ≡ r →
    e1 ; p ≡ q →
    e0 ∘ e1 ; p ≡ r

| maps_sym e p q:
    e ; p ≡ q →
    sym e ; q ≡ p

| maps_beta x A e0 e1 e0':
    substs x e1 e0 e0' →
    beta x A e0 e1 ; app (lam x A e0) e1 ≡ e0'

where "x ; A ≡ B" := (maps x A B).

Function
  st (e: term): option (term * term) :=
  match e with
  | var x => Some (var x, var x)

  | all y A e =>
    if st  A is Some (sA, tA)
    then
      if st  e is Some (se, te)
      then
        Some (all y sA se, all y tA te)
      else
        None
    else
      None

  | lam y A e =>
    if st  A is Some (sA, tA)
    then
      if st  e is Some (se, te)
      then
        Some (lam y sA se, lam y tA te)
      else
        None
    else
      None

  | app e0 e1 =>
    if st  e0 is Some (se0, te0)
    then
      if st  e1 is Some (se1, te1)
      then
        Some (app se0 se1, app te0 te1)
      else
        None
    else
      None

  | e0 ∘ e1 =>
    if st  e0 is Some (se0, te0)
    then
      if st  e1 is Some (se1, te1)
      then
        if term_dec se0 te1
        then
          Some (se1, te0)
        else
          None
      else
        None
    else
      None

  | sym e =>
    if st  e is Some (se, te)
    then
      Some (te, se)
    else
      None

  | beta y A f e => Some (app (lam y A f) e, [y := e] f)

  | _ => Some (e, e)
  end.

Definition st_complete:
  ∀ {e A B},
  Some (A, B) = st e →
  e ; A ≡ B.
Proof.
  intros e.
  functional induction (st e).
  all: intros ? ? p.
  all: cbn in *.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: try eauto.
  - apply subst_sound.
    reflexivity.
  - destruct e.
    all: try contradiction.
    all: econstructor.
Defined.

Definition st_sound:
  ∀ {e A B},
  e ; A ≡ B →
  Some (A, B) = st e.
Proof.
  intros e.
  induction e.
  all: intros ? ? p.
  all: cbn in *.
  all: inversion p.
  all: subst.
  all: try reflexivity.
  - rewrite <- (IHe1 _ _ H4).
    rewrite <- (IHe2 _ _ H5).
    reflexivity.
  - rewrite <- (IHe1 _ _ H4).
    rewrite <- (IHe2 _ _ H5).
    reflexivity.
  - rewrite <- (IHe1 _ _ H1).
    rewrite <- (IHe2 _ _ H4).
    reflexivity.
  - rewrite <- (IHe1 _ _ H1).
    rewrite <- (IHe2 _ _ H4).
    destruct (term_dec q q).
    2: contradiction.
    reflexivity.
  - rewrite <- (IHe _ _ H0).
    reflexivity.
  - rewrite (subst_complete H5).
    reflexivity.
Defined.

Reserved Notation "Γ ⊢ x ∈ A" (at level 80).

Inductive
  types (Γ: string → term): term → term → Type :=
| types_var x: Γ ⊢ var x ∈ Γ x
| types_ofU u: Γ ⊢ ofU u ∈ ofU (succU u)

| types_all {K L x A B}:
    Γ ⊢ A ∈ K →
    put x A Γ ⊢ B ∈ L →
    Γ ⊢ all x A B ∈ L

| types_lam K x A B e:
    Γ ⊢ A ∈ K →
    put x A Γ ⊢ e ∈ B →
    Γ ⊢ lam x A e ∈ all x A B

| types_app x e0 e1 A B:
    Γ ⊢ e0 ∈ all x A B →
    Γ ⊢ e1 ∈ A →
    Γ ⊢ app e0 e1 ∈ [x := e1] B

| types_compose A B e0 e1:
    Γ ⊢ e0 ∈ A →
    Γ ⊢ e1 ∈ B →
    Γ ⊢ e0 ∘ e1 ∈ (A ∘ B)
| types_sym A e:
    Γ ⊢ e ∈ A →
    Γ ⊢ sym e ∈ A
| types_beta x A B e0 e1:
    Γ ⊢ app (lam x A e0) e1 ∈ B →
    Γ ⊢ [x := e1] e0 ∈ B →
    Γ ⊢ beta x A e0 e1 ∈ B

(* | types_cast K e0 e1 A B : *)
(*     Γ ⊢ e0 ∈ K → *)
(*     e0 ; A ≡ B → *)
(*     Γ ⊢ e1 ∈ A → *)
(*     Γ ⊢ e1 ∈ B *)
where "Γ ⊢ x ∈ A" := (types Γ x A).


Definition subst_preserves_equiv:
  ∀ {x s e p q},
    s ; s ≡ s →
    e ; p ≡ q →
    [x := s] e ; [x := s] p ≡ [x := s] q.
Proof.
  intros x s e.
  induction e.
  all: intros ? ? sobj r.
  all: inversion r.
  all: cbn in *.
  all: subst.
  all: auto.
  all: try destruct (string_dec x x0).
  all: subst.
  all: try (econstructor;eauto).
  1: apply sobj.
Admitted.


Inductive normal: term → Type :=
| norm_ofU u: normal (ofU u)
| norm_all x A e:
    normal A → normal e → normal (all x A e)
| norm_var x:
    normal (var x)
| norm_lam x A e:
    normal A → normal e →
    normal (lam x A e)
| norm_app e0 e1:
    (∀ x A e, e0 ≠ lam x A e) →
    normal e0 → normal e1 →
    normal (app e0 e1)
.

Inductive nn: term → Type :=
| nn_beta x A e0 e1:
    nn (app (lam x A e0) e1)

| nn_all x A e0:
    nn A + nn e0 →
    nn (all x A e0)
| nn_lam x A e0:
    nn A + nn e0 →
    nn (lam x A e0)
| nn_app e0 e1:
    nn e0 + nn e1 →
    nn (app e0 e1)
.

Reserved Notation "A ~> B" (at level 80).
Inductive
  step: term → term → Type :=
| step_beta {x A e0 e1 e0'}:
    substs x e0 e1 e0' →
    app (lam x A e0) e1 ~> e0'

| step_all_l {x A A' e0}:
    A ~> A' →
    all x A e0 ~> all x A' e0
| step_all_r {x A e0 e0'}:
    e0 ~> e0' →
    all x A e0 ~> all x A e0'

| step_lam_l {x A A' e0}:
    A ~> A' →
    lam x A e0 ~> lam x A' e0
| step_lam_r {x A e0 e0'}:
    e0 ~> e0' →
    lam x A e0 ~> lam x A e0'

| step_app_l {e0 e1 e0'}:
    e0 ~> e0' →
    app e0 e1 ~> app e0' e1
| step_app_r {e0 e1 e1'}:
    e1 ~> e1' →
    app e0 e1 ~> app e0 e1'
where "A ~> B" := (step A B).

Reserved Notation "A ~>* B" (at level 80).
Inductive
  big: term → term → Type :=
| halt {A}: A ~>* A
| next {A B C}: A ~> B → B ~>* C → A ~>* C
where "A ~>* B" := (big A B).

Function eval e :=
  match e with
  | app (lam x A e0) e1 => Some (subst x e0 e1)

  | app e0 e1 =>
    if eval e0 is Some e0'
    then
      Some (app e0' e1)
    else
      if eval e1 is Some e1'
      then
        Some (app e0 e1')
      else
        None

  | all x A e =>
    if eval A is Some A'
    then
      Some (all x A' e)
    else
      if eval e is Some e'
      then
        Some (all x A e')
      else
        None

  | lam x A e =>
    if eval A is Some A'
    then
      Some (lam x A' e)
    else
      if eval e is Some e'
      then
        Some (lam x A e')
      else
        None

  | _ => None
  end.

Definition eval_sound:
  ∀ {e e'}, Some e' = eval e →
  e ~> e'.
Proof.
  intros e.
  functional induction (eval e).
  all: intros ? p.
  all: cbn in *.
  all: inversion p.
  all: subst.
  all: cbn in *.
  all: try econstructor.
  all: try eauto.
  apply subst_sound.
  reflexivity.
Defined.

Definition eval_complete:
  ∀ {e e'}, e ~> e' →
  eval e = Some e'.
Proof.
  intros e.
  induction e.
  all: cbn in *.
  all: intros e' p.
  all: inversion p.
  all: subst.
  all: try (set (q := IHe1 _ H3); rewrite q).
  all: try (set (q := IHe2 _ H3); rewrite q).
  all: try (set (q := IHe1 _ H2); rewrite q).
  all: try (set (q := IHe2 _ H2); rewrite q).
  all: try reflexivity.
Admitted.

Definition preserve_equiv:
  ∀ {e e'},
    e ~> e' →
    ∀ {A B},
    e ; A ≡ B → e' ; A ≡ B.
Proof.
  intros e.
  induction e.
  all: intros e' p.
  all: inversion p.
  all: subst.
  all: intros ? ? q.
  all: inversion q.
  all: subst.
  all: try econstructor.
  all: try eauto.
  inversion H1.
  subst.
Admitted.

Definition preservation:
  ∀ {e e'},
    e ~> e' →
    ∀ {Γ A},
    Γ ⊢ e ∈ A → Γ ⊢ e' ∈ A.
Proof.
  intros e.
  induction e.
  all: intros e' p.
  all: inversion p.
  all: subst.
  all: intros Γ T q.
  all: inversion q.
  all: subst.
Admitted.

Definition progress:
  ∀ {e},
    nn e →
    ∀ Γ A, Γ ⊢ e ∈ A →
    Σ e', e ~> e'.
Proof.
  intros e.
  all: induction e.
  all: intros p.
  all: inversion p.
  all: subst.
  all: intros Γ T q.
  all: inversion q.
  all: subst.
  - destruct H0.
    + destruct (IHe1 n Γ _ H4) as [e1' r].
      exists (all x e1' e2).
      econstructor.
      auto.
    + destruct (IHe2 n _ _ H5) as [e2' r].
      exists (all x e1 e2').
      econstructor.
      auto.
Admitted.


Example id := lam "A" set (lam "x" (var "A") (var "x")).

Definition tr A := ∀ (B: Prop), (A → B) → B.

Program
Fixpoint normalize {Γ A} e (p: Γ ⊢ e ∈ A) {measure e (λ x y, tr (y ~>* x))} :=
  if eval e is Some e'
  then
    normalize e' (preservation (eval_sound _) p)
  else
    e.

Next Obligation.
Proof.
  intros ? k.
  apply k.
  refine (next _ halt).
  apply eval_sound.
  auto.
Defined.

Next Obligation.
Proof.
Admitted.
