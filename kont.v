#[global]
Set Primitive Projections.
#[global]
Unset Printing Primitive Projection Parameters.

#[global]
Set Universe Polymorphism.
#[global]
Set Polymorphic Inductive Cumulativity.

#[global]
Set Default Goal Selector "!".

Require Coq.Unicode.Utf8.
Require Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Coq.Strings.String.
Require Coq.Bool.Bool.

Require FunInd.

Import Utf8.

Import IfNotations.

Import PeanoNat Nat.

Import FunInd.

Reserved Notation "[ x := s ]".

Reserved Notation "A · B" (at level 80).

Reserved Notation "A × B" (at level 30).
Reserved Notation "⟨ x , y , .. , z ⟩".
Reserved Notation "[ x ; y ; .. ; z ]".

Reserved Notation "Γ |→ x 'in' A" (at level 30).
Reserved Notation "Γ ⊢ e 'in' A" (at level 90).

Reserved Notation "Γ ⊢ A '▹β' B" (at level 90).
Reserved Notation "Γ ⊢ A '▹map' B" (at level 90).
Reserved Notation "Γ ⊢ A ▹ B" (at level 90).

Variant U := set | type (_: nat).

(* Not sure of the categorical semantics I want.

I have a suspicion I want a concept somewhat like "Star Autonomous
Category" but slightly weaker.

I have an idea of something like call by push value but instead of an
adjunction F |- U between categories C and D I want between C and
D^op.

C would be a category of values, D would be a category of
effects/continuations.

F would be a continuation popping a value off the stack and U would be
a thunk.
*)
Inductive term :=
| var (x: String.string)

| ofU (u: U)

| unit
| void

| prod (v0 v1: term)
| sum (v0 v1: term)
| exp (v0 v1: term)

| tt
| fanout (v0 v1: term)
| π1 (v: term)
| π2 (v: term)

| abort
| fanin (k0 k1: term)
| i1 (k: term)
| i2 (k: term)

| lam (x: String.string) (A v: term)
| app (v0 v1: term)

| jump (k v: term)
| thunk (j: String.string) (A s: term)
| pop (x: String.string) (A s: term)
.
Coercion ofU: U >-> term.

Notation "⊤" := unit.
Notation "⊥" := void.

Infix "+" := sum.
Infix "×" := prod.

Notation "⟨ x , y , .. , z ⟩" := (fanout .. (fanout x y) .. z).
Notation "[ x ; y ; .. ; z ]" := (fanin .. (fanin x y) .. z).

Infix "·" := jump.

Definition S u :=
  match u with
  | set => type 0
  | type n => type (Datatypes.S n)
  end.

Definition U_dec (x y: U): {x = y} + {x <> y}.
Proof.
  set (n := Nat.eq_dec).
  decide equality.
Defined.

Definition term_eq_dec (x y: term): {x = y} + {x <> y}.
Proof.
  set (s := String.string_dec).
  set (u := U_dec).
  decide equality.
Defined.

Function subst (x: String.string) s e :=
  match e with
  | var y => if String.string_dec x y then s else e

  | k · v => subst x s k · subst x s v

  | thunk y A t =>
    if String.string_dec x y
    then
      thunk y (subst x s A) t
    else
      thunk y (subst x s A) (subst x s t)

  | pop y A t =>
    if String.string_dec x y
    then
      pop y (subst x s A) t
    else
      pop y (subst x s A) (subst x s t)

  | v0 × v1 => (subst x s v0) × (subst x s v1)
  | v0 + v1 => (subst x s v0) + (subst x s v1)
  | exp v0 v1 => exp (subst x s v0) (subst x s v1)

  | ⟨v0, v1⟩ => ⟨subst x s v0, subst x s v1⟩
  | π1 v => π1 (subst x s v)
  | π2 v => π2 (subst x s v)

  | [v0; v1] => [subst x s v0; subst x s v1]
  | i1 v => i1 (subst x s v)
  | i2 v => i2 (subst x s v)

  | lam y A t =>
    if String.string_dec x y
    then
      lam y (subst x s A) t
    else
      lam y (subst x s A) (subst x s t)

  | app v0 v1 => app (subst x s v0) (subst x s v1)

  | _ => e
  end.

Notation "[ x := s ]" := (subst x s).

Variant sort := stmt | val (_: term) | kont (_: term).
Notation "#" := val.
Notation "$" := kont.
Notation "!" := stmt.

Definition env := String.string → sort.

Definition update x A (e: env): env := λ y,
  if String.string_dec x y then A else e y.

Notation "Γ |→ x 'in' A" := (update x A Γ).

Inductive judge: env → term → sort → Prop :=
| judge_var {Γ x}: Γ ⊢ var x in Γ x

| judge_ofU {Γ} {u: U}: Γ ⊢ u in # (S u)

| judge_unit {Γ}: Γ ⊢ ⊤ in # set
| judge_void {Γ}: Γ ⊢ ⊥ in # set

| judge_sum {Γ K A B}:
  Γ ⊢ A in # (ofU K) →
  Γ ⊢ B in # (ofU K) →
  Γ ⊢ A + B in # (ofU K)
| judge_prod {Γ K A B}:
  Γ ⊢ A in # (ofU K) →
  Γ ⊢ B in # (ofU K) →
  Γ ⊢ A × B in # (ofU K)
| judge_exp {Γ K A B}:
  Γ ⊢ A in # (ofU K) →
  Γ ⊢ B in # (ofU K) →
  Γ ⊢ exp A B in # (ofU K)

| judge_tt {Γ}: Γ ⊢ tt in # ⊤
| judge_fanout {Γ A B e0 e1}:
  Γ ⊢ e0 in # A →
  Γ ⊢ e1 in # B →
  Γ ⊢ ⟨e0, e1⟩ in # (A × B)
| judge_π1 {Γ A B e}:
  Γ ⊢ e in # (A × B) →
  Γ ⊢ π1 e in # A
| judge_π2 {Γ A B e}:
  Γ ⊢ e in # (A × B) →
  Γ ⊢ π2 e in # B

| judge_lam {Γ} {x u A B e}:
  Γ ⊢ A in # (ofU u) →
  Γ |→ x in # A ⊢ e in # B →
  Γ ⊢ lam x A e in # (exp A B)
| judge_app {Γ} {A B e0 e1}:
  Γ ⊢ e0 in # (exp A B) →
  Γ ⊢ e1 in # A →
  Γ ⊢ app e0 e1 in # B

| judge_abort {Γ}: Γ ⊢ abort in $ void
| judge_fanin {Γ A B e0 e1}:
  Γ ⊢ e0 in $ A →
  Γ ⊢ e1 in $ B →
  Γ ⊢ [e0; e1] in $ (A + B)
| judge_i1 {Γ A B e}:
  Γ ⊢ e in $ (A + B) →
  Γ ⊢ i1 e in $ A
| judge_i2 {Γ A B e}:
  Γ ⊢ e in $ (A + B) →
  Γ ⊢ i2 e in $ B

| judge_jump {Γ A k e}:
  Γ ⊢ k in $ A →
  Γ ⊢ e in # A →
  Γ ⊢ k · e in !
| judge_pop {Γ} {x A e u}:
  Γ ⊢ A in # (ofU u) →
  Γ |→ x in # A ⊢ e in ! →
  Γ ⊢ pop x A e in $ A
| judge_thunk {Γ} {k A e u}:
  Γ ⊢ A in # (ofU u) →
  Γ |→ k in $ A ⊢ e in ! →
  Γ ⊢ thunk k A e in # A
where "Γ ⊢ e 'in' s" := (judge Γ e s)
.

Variant ispop: term → Prop :=
| ispopof {x A s}: ispop (pop x A s).

Inductive beta: env → term → term → Prop :=
| bvta_app_lam {Γ x A v0 v1}:
  Γ ⊢ app (lam x A v1) v0 ▹β [x := v0] v1

| beta_jump_pop {Γ x A s v}:
  Γ ⊢ pop x A s · v ▹β [x := v] s
(* disambiguate evaluation order *)
| beta_jump_thunk {Γ j A s k}:
  not (ispop k) →
  Γ ⊢ k · thunk j A s ▹β [j := k] s

| bvta_π1_fanout {Γ v0 v1}: Γ ⊢ π1 ⟨v0, v1⟩ ▹β v0
| bvta_π2_fanout {Γ v0 v1}: Γ ⊢ π2 ⟨v0, v1⟩ ▹β v1

| bkta_i1_fanin {Γ k0 k1}: Γ ⊢ i1 [k0; k1] ▹β k0
| bkta_i2_fanin {Γ k0 k1}: Γ ⊢ i2 [k0; k1] ▹β k1
where "Γ ⊢ A '▹β' B" := (beta Γ A B).

Inductive step: env → term → term → Prop :=
| step_beta {Γ e e'}:
  Γ ⊢ e ▹β e' →
  Γ ⊢ e ▹ e'

| step_map {Γ e e'}:
  Γ ⊢ e ▹map e' →
  Γ ⊢ e ▹ e'
where "Γ ⊢ A ▹ B" := (step Γ A B)

with map: env → term → term → Prop :=
| map_jump_l {Γ k k' v}:
  Γ ⊢ k ▹map k' →
  Γ ⊢ k·v ▹map k'·v
| map_jump_r {Γ k v v'}:
  Γ ⊢ v ▹map v' →
  Γ ⊢ k·v ▹map k·v'

| map_fanout_l {Γ v0 v0' v1}:
  Γ ⊢ v0 ▹map v0' →
  Γ ⊢ ⟨v0, v1⟩ ▹map ⟨v0', v1⟩
| map_fanout_r {Γ v0 v1 v1'}:
  Γ ⊢ v1 ▹map v1' →
  Γ ⊢ ⟨v0, v1⟩ ▹map ⟨v0, v1'⟩

| map_π1 {Γ v v'}:
  Γ ⊢ v ▹map v' →
  Γ ⊢ π1 v ▹map π1 v'
| map_π2 {Γ v v'}:
  Γ ⊢ v ▹map v' →
  Γ ⊢ π2 v ▹map π2 v'

| map_fanin_l {Γ k0 k0' k1}:
  Γ ⊢ k0 ▹map k0' →
  Γ ⊢ [k0; k1] ▹map [k0'; k1]
| map_fanin_r {Γ k0 k1 k1'}:
  Γ ⊢ k1 ▹map k1' →
  Γ ⊢ [k0; k1] ▹map [k0; k1']

| map_i1 {Γ k k'}:
  Γ ⊢ k ▹map k' →
  Γ ⊢ i1 k ▹map i1 k'
| map_i2 {Γ k k'}:
  Γ ⊢ k ▹map k' →
  Γ ⊢ i2 k ▹map i2 k'

| map_thunk_l {Γ x A A' s}:
  Γ ⊢ A ▹map A' →
  Γ ⊢ thunk x A s ▹map thunk x A' s
| map_thunk_r {Γ x A s s'}:
  Γ |→ x in $ A ⊢ s ▹map s' →
  Γ ⊢ thunk x A s ▹map thunk x A s'

| map_pop_l {Γ x A A' s}:
  Γ ⊢ A ▹map A' →
  Γ ⊢ pop x A s ▹map pop x A' s
| map_pop_r {Γ x A s s'}:
  Γ |→ x in # A ⊢ s ▹map s' →
  Γ ⊢ pop x A s ▹map pop x A s'

| map_lam_l {Γ x A A' v}:
  Γ ⊢ A ▹map A' →
  Γ ⊢lam x A v ▹map lam x A' v
| map_lam_r {Γ x A v v'}:
  Γ |→ x in # A ⊢ v ▹map v' →
  Γ ⊢lam x A v ▹map lam x A v'

| map_app_l {Γ v0 v0' v1}:
  Γ ⊢ v0 ▹map v0' →
  Γ ⊢ app v0 v1 ▹map app v0' v1
| map_app_r {Γ v0 v1 v1'}:
  Γ ⊢ v1 ▹map v1' →
  Γ ⊢ app v0 v1 ▹map app v0 v1'

| map_step {Γ e e'}:
  Γ ⊢ e ▹ e' →
  Γ ⊢ e ▹map e'

where "Γ ⊢ A ▹map B" := (map Γ A B).

Function prim (e: term): option term :=
  match e with
  | app (lam x _ v0) v1 => Some ([x := v1] v0)

  | pop x _ s · v => Some ([x := v] s)
  | k · thunk x _ s => Some ([x := k] s)

  | π1 ⟨v, _⟩ => Some v
  | π2 ⟨_, v⟩ => Some v

  | i1 [k; _] => Some k
  | i2 [_; k] => Some k

  | _ => None
  end.

Function eval (Γ: env) (e: term): option term :=
  if prim e is Some e'
  then Some e'
  else
  match e with
  | jump k v =>
     if eval Γ k is Some k'
     then
         Some (k' · v)
     else
         if eval Γ v is Some v'
         then
           Some (k · v')
         else
           None

  | ⟨e0, e1⟩ =>
    if eval Γ e0 is Some e0'
    then
      Some ⟨e0', e1⟩
    else
      if eval Γ e1 is Some e1'
      then
        Some ⟨e0, e1'⟩
      else
        None

  | π1 e =>
     if eval Γ e is Some e'
     then
       Some (π1 e')
     else
       None

  | π2 e =>
     if eval Γ e is Some e'
     then
       Some (π2 e')
     else
       None

  | [e0; e1] =>
    if eval Γ e0 is Some e0'
    then
      Some [e0'; e1]
    else
      if eval Γ e1 is Some e1'
      then
        Some [e0; e1']
      else
        None

  | i1 e =>
     if eval Γ e is Some e'
     then
       Some (i1 e')
     else
       None

  | i2 e =>
     if eval Γ e is Some e'
     then
       Some (i2 e')
     else
       None

  | thunk x A s =>
      if eval Γ A is Some A'
      then
        Some (thunk x A' s)
      else
        if eval (Γ |→ x in $ A) s is Some s'
        then
          Some (thunk x A s')
        else
          None

  | pop x A s =>
      if eval Γ A is Some A'
      then
        Some (pop x A' s)
      else
        if eval (Γ |→ x in # A) s is Some s'
        then
          Some (pop x A s')
        else
          None

  | lam x A v =>
      if eval Γ A is Some A'
      then
        Some (lam x A' v)
      else
        if eval (Γ |→ x in # A) v is Some v'
        then
          Some (lam x A v')
        else
          None

  | app v0 v1 =>
      if eval Γ v0 is Some v0'
      then
        Some (app v0' v1)
      else
        if eval Γ v1 is Some v1'
        then
          Some (app v0 v1')
        else
          None

  | _ => None
  end.

Lemma prim_sound: ∀ {e Γ e'},
  prim e = Some e' →
  Γ ⊢ e ▹β e'.
Proof.
  intros e.
  functional induction (prim e).
  all: intros ? ? p.
  all: inversion p.
  all: econstructor.
  intro q.
  destruct q.
  auto.
Qed.

Lemma prim_complete: ∀ {e Γ e'},
  Γ ⊢ e ▹β e' →
  prim e = Some e'.
Proof.
  intros ? ? ? p.
  induction p.
  all: try reflexivity.
  all: try reflexivity.
  destruct k.
  all: try reflexivity.
  cbn.
  refine (match (H _) with end).
  exists.
Qed.

Theorem eval_sound: ∀ {e Γ e'},
  eval Γ e = Some e' →
  Γ ⊢ e ▹ e'.
Proof.
  intros e Γ.
  functional induction (eval Γ e).
  all: intros ? p.
  all: inversion p.
  all: subst.
  1: apply step_beta.
  1: apply prim_sound.
  1: auto.
  all: apply step_map.
  all: econstructor; eauto.
  all: try apply map_step.
  all: try apply IHo.
  all: auto.
Qed.

Theorem eval_complete: ∀ {e Γ e'},
  Γ ⊢ e ▹ e' →
  eval Γ e = Some e'.
Proof.
  intros ? ? ? p.
  induction p.
Admitted.

Function typeof (Γ: env) (e: term): option sort :=
  match e with
  | var x => Some (Γ x)

  | k · e =>
    if typeof Γ k is Some ($ A)
    then
      if typeof Γ e is Some (# A')
      then
        if term_eq_dec A A'
        then
          Some !
        else
          None
      else
        None
    else
      None

  | ofU u => Some (# (ofU (S u)))
  | ⊤ => Some (# (ofU set))
  | ⊥ => Some (# (ofU set))

  | A + B =>
    if typeof Γ A is Some (# (ofU K))
    then
      if typeof Γ B is Some (# (ofU K'))
      then
        if U_dec K K'
        then
          Some (# (ofU K))
        else
          None
      else
        None
    else
      None
  | A × B =>
    if typeof Γ A is Some (# (ofU K))
    then
      if typeof Γ B is Some (# (ofU K'))
      then
        if U_dec K K'
        then
          Some (# (ofU K))
        else
          None
      else
        None
    else
      None

  | exp A B =>
    if typeof Γ A is Some (# (ofU K))
    then
      if typeof Γ B is Some (# (ofU K'))
      then
        if U_dec K K'
        then
          Some (# (ofU K))
        else
          None
      else
        None
    else
      None

  | thunk x A e =>
    if typeof Γ A is Some (# (ofU _))
    then
      if typeof (Γ |→ x in $ A) e is Some !
      then
        Some (# A)
      else
        None
    else
      None

  | lam x A v =>
    if typeof Γ A is Some (# (ofU _))
    then
      if typeof (Γ |→ x in # A) v is Some (# B)
      then
        Some (# (exp A B))
      else
        None
    else
      None

  | app v0 v1 =>
    if typeof Γ v0 is Some (# (exp A B))
    then
      if typeof Γ v1 is Some (# A')
      then
        if term_eq_dec A A'
        then
          Some (# B)
        else
          None
      else
        None
    else
      None

  | tt => Some (# unit)
  | fanout e0 e1 =>
    if typeof Γ e0 is Some (# A)
    then
      if typeof Γ e1 is Some (# B)
      then
        Some (# (A × B))
      else
        None
    else
      None
  | π1 e =>
    if typeof Γ e is Some (# (A × _))
    then
      Some (# A)
    else
      None
  | π2 e =>
    if typeof Γ e is Some (# (_ × A))
    then
      Some (# A)
    else
      None

  | pop x A e =>
    if typeof Γ A is Some (# (ofU _))
    then
      if typeof (Γ |→ x in # A) e is Some !
      then
        Some ($ A)
      else
        None
    else
      None

  | abort => Some ($ void)
  | fanin e0 e1 =>
    if typeof Γ e0 is Some ($ A)
    then
      if typeof Γ e1 is Some ($ B)
      then
        Some ($ (A + B))
      else
        None
    else
      None
  | i1 e =>
    if typeof Γ e is Some ($ (A + _))
    then
      Some ($ A)
    else
      None
  | i2 e =>
    if typeof Γ e is Some ($ (_ + A))
    then
      Some ($ A)
    else
      None
  end.

Definition mt: env := λ _, !.

Theorem typeof_sound: ∀ {Γ e s},
  typeof Γ e = Some s →
  Γ ⊢ e in s.
Proof.
  intros Γ e.
  functional induction (typeof Γ e).
  all: intros ? p.
  all: inversion p.
  all: try econstructor; eauto.
Qed.

Theorem typeof_complete: ∀ {e Γ s},
    Γ ⊢ e in s →
    typeof Γ e = Some s.
Proof.
  intros ? ? ? p.
  induction p.
  all: cbn.
  all: try reflexivity.
  all: try rewrite IHp1.
  all: try rewrite IHp2.
  all: try rewrite IHp.
  all: try reflexivity.
  - destruct (U_dec K K).
    + reflexivity.
    + contradiction.
  - destruct (U_dec K K).
    + reflexivity.
    + contradiction.
  - destruct (U_dec K K).
    + reflexivity.
    + contradiction.
  - destruct (term_eq_dec A A).
    1: reflexivity.
    contradiction.
  - destruct (term_eq_dec A A).
    1: reflexivity.
    contradiction.
Qed.

Definition ofty s := { e | mt ⊢ e in s }.

Definition tc (e: term):
  if typeof mt e is Some s
  then
    ofty s
  else
    Datatypes.unit.
Proof.
  destruct (typeof mt e) eqn:q.
  2: constructor.
  exists e.
  apply typeof_sound.
  assumption.
Qed.


Require Koika.IdentParsing.

Import IdentParsing.TC.

Reserved Notation "'THUNK' ( k : A ) , s" (k name, at level 200).
Reserved Notation "'POP' ( k : A ) , s" (k name, at level 200).
Reserved Notation "'LAM' ( k : A ) , s" (k name, at level 200).

Notation "'THUNK' ( k : A ) , s" := (thunk (ident_to_string k) A (let k : term := var (ident_to_string k) in s)).
Notation "'POP' ( k : A ) , s" := (pop (ident_to_string k) A (let k : term := var (ident_to_string k) in s)).
Notation "'LAM' ( k : A ) , s" := (lam (ident_to_string k) A (let k : term := var (ident_to_string k) in s)).

Definition bool := unit + unit.

Definition true: ofty (# bool) := tc (
  THUNK (k: bool),
  i1 k · tt
).
Definition false: ofty (# bool) := tc (
  THUNK (k: bool),
  i2 k · tt
).
