#[global]
Set Primitive Projections.
#[global]
Unset Printing Primitive Projection Parameters.

#[global]
Set Universe Polymorphism.

#[global]
Set Default Goal Selector "!".

Require Import Coq.Unicode.Utf8.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Strings.String.

(* Prototype an approach based around "structured cospans" *)
Class Term := {
  T: Type ;
  T_Setoid: Setoid T ;

  mt: T ;
  trv: T ;
  sum: T → T → T ;
  prod: T → T → T ;
  exp: T → T → T ;

  sum_Proper: Proper (equiv ==> equiv ==> equiv) sum ;
  prod_Proper: Proper (equiv ==> equiv ==> equiv) prod ;
  exp_Proper: Proper (equiv ==> equiv ==> equiv) exp ;
}.
Coercion T: Term >-> Sortclass.

Existing Instance T_Setoid.
Existing Instance sum_Proper.
Existing Instance prod_Proper.
Existing Instance exp_Proper.

Notation "∅" := mt.
Notation "·" := trv.

Infix "+" := sum.
Infix "*" := prod.
Infix "^" := exp.

Class Homomorphism {A B: Term} (f: A → B): Prop := {
  map_Proper: Proper (equiv ==> equiv) f ;
  map_mt: f ∅ == ∅ ;
  map_trv: f · == · ;
  map_sum x y: f (x + y) == f x + f y ;
  map_prod x y: f (x * y) == f x * f y ;
  map_exp x y: f (exp x y) == exp (f x) (f y) ;
}.

Existing Instance map_Proper.

Module Import Hom.
  Definition Hom (A B: Term) := { f: A → B | Homomorphism f}.

  #[program]
   Definition id A : Hom A A := λ x, x.

  Next Obligation.
  Proof.
  Admitted.
End Hom.

Module Terminal.
  #[refine]
  Instance terminal_Setoid: Setoid unit := {
    equiv _ _ := True ;
  }.
  Proof.
    exists.
    all: exists.
  Defined.

  #[refine]
  Instance Terminal: Term := {
    T := unit ;
    mt := tt ;
    trv := tt ;
    sum _ _ := tt ;
    prod _ _ := tt ;
    exp _ _ := tt ;
  }.
  Proof.
    all: intros ? ? ? ? ? ?.
    all: reflexivity.
  Defined.
End Terminal.

Module Free.
  #[universes(cumulative)]
   Inductive free {U: Type} :=
  | η (u: U)
  | mt | trv
  | sum (A B: free)
  | prod (A B: free)
  | exp (B A: free)
  .
  Arguments free: clear implicits.

  Instance free_Setoid U: Setoid (free U) := {
    equiv := eq ;
  }.

  Instance Free U: Term := {
    T := free U ;
    mt := mt ;
    trv := trv ;
    sum := sum ;
    prod := prod ;
    exp := exp ;
  }.

  #[program]
  Definition map {A B} (f: A → B): Hom (Free A) (Free B) :=
    fix loop x :=
      match x with
      | η u => η (f u)
      | mt => mt
      | trv => trv
      | sum A B => sum (loop A) (loop B)
      | prod A B => prod (loop A) (loop B)
      | exp A B => exp (loop A) (loop B)
      end.
  Next Obligation.
  Proof.
    exists.
    all: cbn.
    all: try reflexivity.

    intros x y p.
    induction x.
    all: inversion p.
    all: subst.
    all: cbn.
    all: try reflexivity.
  Qed.
End Free.

Module Pullback.
  Definition pullback {A B C} (f: Hom A C) (g: Hom B C) :=
    { '(x, y) | proj1_sig f x == proj1_sig g y }.

  #[program]
  Instance pullback_Setoid {A B C} (f: Hom A C) (g: Hom B C): Setoid (pullback f g) := {
    equiv x y := fst (proj1_sig x) == fst (proj1_sig y) ∧ snd (proj1_sig x) == snd (proj1_sig y) ;
  }.
  Next Obligation.
  Proof.
    exists.
    - intros ?.
      split.
      all: reflexivity.
    - intros ? ? p.
      destruct p.
      split.
      all: symmetry.
      all: auto.
    - intros ? ? ? p q.
      destruct p as [p1 p2], q as [q1 q2].
      rewrite p1,p2,q1,q2.
      split.
      all: reflexivity.
  Defined.

  #[program]
  Instance Pullback {A B C} (f: Hom A C) (g: Hom B C): Term := {
    T := pullback f g ;
    mt := (∅, ∅) ;
    trv := (·, ·) ;
    sum A B := (fst A + fst B, snd A + snd B) ;
    prod A B := (fst A * fst B, snd A * snd B) ;
    exp A B := (fst A ^ fst B, snd A ^ snd B) ;
  }.

  Next Obligation.
  Proof.
    destruct f, g.
    cbn.
    repeat rewrite map_mt.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    destruct f, g.
    cbn.
    repeat rewrite map_trv.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    destruct f as [f fp], g as [g p],
             A as [[A1 A2] Ap], B as [[B1 B2] Bp].
    cbn in *.
    repeat rewrite map_sum.
    rewrite Ap, Bp.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    destruct f as [f fp], g as [g p],
             A as [[A1 A2] Ap], B as [[B1 B2] Bp].
    cbn in *.
    repeat rewrite map_prod.
    rewrite Ap, Bp.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    destruct f as [f fp], g as [g p],
             A as [[A1 A2] Ap], B as [[B1 B2] Bp].
    cbn in *.
    repeat rewrite map_exp.
    rewrite Ap, Bp.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    intros x x' p y y' q.
    cbn in *.
    destruct x as [[x1 x2] xp],
             x' as [[x1' x2'] xp'],
             y as [[y1 y2] yp],
                  y' as [[y1' y2'] yp'].
    cbn in *.
    destruct p as [p1 p2], q as [q1 q2].
    cbn in *.
    rewrite p1, p2, q1, q2.
    split.
    all: reflexivity.
  Qed.

  Next Obligation.
  Proof.
    intros x x' p y y' q.
    cbn in *.
    destruct x as [[x1 x2] xp],
             x' as [[x1' x2'] xp'],
             y as [[y1 y2] yp],
                  y' as [[y1' y2'] yp'].
    cbn in *.
    destruct p as [p1 p2], q as [q1 q2].
    cbn in *.
    rewrite p1, p2, q1, q2.
    split.
    all: reflexivity.
  Qed.

  Next Obligation.
  Proof.
    intros x x' p y y' q.
    cbn in *.
    destruct x as [[x1 x2] xp],
             x' as [[x1' x2'] xp'],
             y as [[y1 y2] yp],
                  y' as [[y1' y2'] yp'].
    cbn in *.
    destruct p as [p1 p2], q as [q1 q2].
    cbn in *.
    rewrite p1, p2, q1, q2.
    split.
    all: reflexivity.
  Qed.
End Pullback.

Module Slice.
  (* Term/S *)
  Record bundle A := {
    s: Term ;
    π: Hom s A ;
  }.

  Arguments s {A}.
  Arguments π {A}.

  Definition slice {S} (A B: bundle S) := { f : s A → s B | Homomorphism f ∧ ∀ x, proj1_sig (π B) (f x) == proj1_sig (π A) x }.

  #[program]
   Definition id {S} (A: bundle S): slice A A := λ x, x.

  Next Obligation.
  Proof.
    split.
    - exists.
      all: try reflexivity.
      intros ? ? ?.
      auto.
    - reflexivity.
  Qed.

  #[program]
   Definition compose {S} {A B C: bundle S} (f: slice B C) (g: slice A B): slice A C :=
    λ x, f (g x).

  Next Obligation.
  Proof.
    destruct f as [f [fH fp]], g as [g [gH gp]].
    cbn in *.
    split.
    - exists.
      + intros ? ? p.
        rewrite p.
        reflexivity.
      + repeat rewrite map_mt.
        reflexivity.
      + repeat rewrite map_trv.
        reflexivity.
      + intros.
        repeat rewrite map_sum.
        reflexivity.
      + intros.
        repeat rewrite map_prod.
        reflexivity.
      + intros.
        repeat rewrite map_exp.
        reflexivity.
    - intros.
      rewrite (fp _).
      rewrite (gp _).
      reflexivity.
  Qed.

  Import Terminal.

  #[program]
  Definition No (S: Term): bundle Terminal := {| π (_: S) := tt |}.

  Next Obligation.
  Proof.
    exists.
    all: try reflexivity.
    intros ? ? p.
    reflexivity.
  Qed.

  #[program]
  Definition map {A B} (f: Hom A B): slice (No A) (No B) := f.

  Next Obligation.
  Proof.
    destruct f as [f fh].
    cbn.
    split.
    - exists.
      + intros ? ? p.
        rewrite p.
        reflexivity.
      + rewrite map_mt.
        reflexivity.
      + rewrite map_trv.
        reflexivity.
      + intros.
        rewrite map_sum.
        reflexivity.
      + intros.
        rewrite map_prod.
        reflexivity.
      + intros.
        rewrite map_exp.
        reflexivity.
    - intros.
      exists.
  Qed.

  Infix "∘" := compose (at level 30).

  #[program]
  Definition basechange {A B: Term} (f: Hom A B) (x: bundle B): bundle A :=
    {| s := Pullback.Pullback f (π x) ;
       π x := fst x |}.

  Next Obligation.
  Proof.
    exists.
    all: cbn.
    all: try reflexivity.
    intros ? ? p.
    destruct p as [p q].
    rewrite p.
    reflexivity.
  Qed.

  #[program]
  Definition Σ {A B: Term} (f: Hom A B) (g: bundle A): bundle B :=
    {| π x := f (π g x) |}.

  Next Obligation.
  Proof.
    destruct f as [f fp], g as [s [g gp]].
    cbn.
    exists.
    all: cbn.
    - intros ? ? p.
      rewrite p.
      reflexivity.
    - repeat rewrite map_mt.
      reflexivity.
    - repeat rewrite map_trv.
      reflexivity.
    - intros.
      repeat rewrite map_sum.
      reflexivity.
    - intros.
      repeat rewrite map_prod.
      reflexivity.
    - intros.
      repeat rewrite map_exp.
      reflexivity.
  Qed.

  #[program]
  Definition Π {A B: Term} (f: Hom A B) (g: bundle A): bundle B :=
    {| s := Pullback.Pullback (π g) (Hom.id _) ;
       π x := f (snd (proj1_sig x)) ; |}.

  Next Obligation.
  Proof.
    destruct f as [f fp].
    destruct g as [s [g gp]].
    cbn.
    exists.
    all: cbn.
    - intros ? ? p.
      destruct p as [p q].
      rewrite q.
      reflexivity.
    - rewrite map_mt.
      reflexivity.
    - rewrite map_trv.
      reflexivity.
    - intros.
      rewrite map_sum.
      reflexivity.
    - intros.
      rewrite map_prod.
      reflexivity.
    - intros.
      rewrite map_exp.
      reflexivity.
  Qed.

  (* Reader monad IIRC *)
  #[program]
  Definition pure {S T} {A: bundle S} (f: Hom S T): slice A (basechange f (Π f A)) :=
    λ x, (proj1_sig (π A) x, (x, proj1_sig (π A) x)).

  Next Obligation.
  Proof.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    destruct A as [sA [A Ap]],
             f as [f fp].
    cbn in *.
    split.
    - exists.
      all: cbn.
      + intros ? ? p.
        cbn.
        repeat rewrite p.
        all: repeat split.
        all: reflexivity.
      + repeat rewrite map_mt.
        all: repeat split.
        all: reflexivity.
      + repeat rewrite map_trv.
        all: repeat split.
        all: reflexivity.
      + intros.
        repeat rewrite map_sum.
        all: repeat split.
        all: reflexivity.
      + intros.
        repeat rewrite map_prod.
        all: repeat split.
        all: reflexivity.
      + intros.
        repeat rewrite map_exp.
        all: repeat split.
        all: reflexivity.
    - intros.
      reflexivity.
  Qed.
End Slice.

Module StructuredSlice.
  Import Slice.
  Import Free.

  Definition Obj S := bundle (Free S).
  Definition Struct {S}: Obj S → Obj S → Type  := @slice (Free S).

  Definition id {S} (A: Obj S) := Slice.id A.
  Definition compose {S} {A B C: Obj S} := @Slice.compose _ A B C.

  Infix "∘" := compose (at level 30).

  Definition Any S: Obj S := {| π := Hom.id _ |}.

  Definition basechange {A B: Type} (f: A → B): Obj B → Obj A :=
    basechange (Free.map f).

  Definition Σ {A B: Type} (f: A → B): Obj A → Obj B :=
    Σ (Free.map f).

  Definition Π {A B: Type} (f: A → B): Obj A → Obj B :=
    Π (Free.map f).

  Definition pure {S T} {A: Obj S} (f: S → T): Struct A (basechange f (Π f A)) :=
    pure (Free.map f).
End StructuredSlice.

Module Span.
  Record span A B := {
    s: Term ;
    π1: Hom s A ;
    π2: Hom s B ;
                    }.

  Arguments s {A B}.
  Arguments π1 {A B}.
  Arguments π2 {A B}.

  #[program]
   Definition id A: span A A := {| π1 x := x ; π2 x := x |}.

  Next Obligation.
  Proof.
    exists.
    all: try reflexivity.
    intros ? ? ?.
    auto.
  Qed.

  Next Obligation.
  Proof.
    exists.
    all: try reflexivity.
    intros ? ? ?.
    auto.
  Qed.

  #[program]
   Definition compose {A B C} (f: span B C) (g: span A B): span A C :=
    {|
    s := Pullback.Pullback (π1 f) (π2 g) ;
    π1 x := proj1_sig (π1 g) (snd (proj1_sig x)) ;
    π2 x := proj1_sig (π2 f) (fst (proj1_sig x)) ;
    |}.

  Next Obligation.
  Proof.
    destruct f as [fs [f1 f1p] [f2 f2p]].
    destruct g as [gs [g1 g1p] [g2 g2p]].
    cbn.
    exists.
    - intros ? ? p.
      destruct p as [p q].
      rewrite q.
      reflexivity.
    - cbn.
      rewrite map_mt.
      reflexivity.
    - cbn.
      rewrite map_trv.
      reflexivity.
    - intros.
      cbn.
      rewrite map_sum.
      reflexivity.
    - intros.
      cbn.
      rewrite map_prod.
      reflexivity.
    - intros.
      cbn.
      rewrite map_exp.
      reflexivity.
  Qed.

  Next Obligation.
  Proof.
    destruct f as [fs [f1 f1p] [f2 f2p]].
    destruct g as [gs [g1 g1p] [g2 g2p]].
    cbn.
    exists.
    - intros ? ? p.
      destruct p as [p q].
      rewrite p.
      reflexivity.
    - cbn.
      rewrite map_mt.
      reflexivity.
    - cbn.
      rewrite map_trv.
      reflexivity.
    - intros.
      cbn.
      rewrite map_sum.
      reflexivity.
    - intros.
      cbn.
      rewrite map_prod.
      reflexivity.
    - intros.
      cbn.
      rewrite map_exp.
      reflexivity.
  Qed.

  #[program]
   Definition transpose {A B} (f: span A B): span B A :=
    {| π1 := π2 f ; π2 := π1 f |}.

  #[program]
  Definition map {A B} (f: Hom A B): span A B := {| π1 x := x ; π2 := f |}.

  Next Obligation.
  Proof.
    exists.
    all: try reflexivity.
    intros ? ? ?.
    auto.
  Qed.

  Infix "∘" := compose (at level 30).
  Notation "f 'ᵀ'" := (transpose f) (at level 1).
End Span.

Module Structured.
  Import Span.
  Import Free.

  Definition Struct A B := span (Free A) (Free B).

  Definition id A := Span.id (Free A).
  Definition compose {A B C} := @Span.compose (Free A) (Free B) (Free C).
  Definition transpose {A B} := @Span.transpose (Free A) (Free B).

  Definition map {A B}: Hom (Free A) (Free B) → Struct A B := Span.map.

  Infix "∘" := compose (at level 30).
  Notation "f 'ᵀ'" := (transpose f) (at level 1).
End Structured.

Import Free.
Import Slice.
Import StructuredSlice.

Open Scope string_scope.

Definition Forsome (x: Obj nat): Obj nat := basechange S (Π S x).
Definition Forall (x: Obj nat): Obj nat := basechange S (Π S x).

(* weird *)
Definition foo: Struct (Any nat) (Forall (Any nat)) := pure S.
