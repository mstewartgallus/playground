Record Poly := {
  pos: Type ;
  dir: pos -> Type ;
}.

Record Mor (P Q: Poly) := {
  mor_pos: pos P -> pos Q ;
  mor_dir x: dir Q (mor_pos x) -> dir P x ;
}.
Arguments mor_pos {P Q}.
Arguments mor_dir {P Q}.

Definition prod A B := {|
  pos := pos A * pos B ;
  dir xy := sum (dir A (fst xy)) (dir B (snd xy)) ;
|}.

Definition sum A B := {|
  pos := pos A + pos B ;
  dir xy :=
    match xy with
    | inl x => dir A x
    | inr x => dir B x
    end ;
|}.

Infix "+" := sum.
Infix "*" := prod.

Definition mt := {|
  dir (x: Empty_set) := match x with end ;
|}.

Definition K A := {|
  dir (x: A) := Empty_set ;
|}.

Definition X := {|
  dir (_: unit) := unit ;
|}.
Definition X2 := {|
  dir (_: unit) := bool ;
|}.

(* quotient by mapping to the presheaf of poly some t, p + X^2 * t *)
Record Dual (P Q: Poly) := {
  ix: Poly -> Poly ;
  mor t: Mor (P + X2 * t) (Q + X2 * ix t);
}.
Arguments ix {P Q}.
Arguments mor {P Q}.

Definition id A: Dual A A := {|
  ix P := P ;
  mor _ := {|
    mor_pos x := x ;
    mor_dir _ y := y ;
  |} ;
|}.

Definition compose {A B C} (f: Dual B C) (g: Dual A B): Dual A C := {|
  ix P := ix f (ix g P) ;
  mor _ := {|
    mor_pos x := mor_pos (mor f _) (mor_pos (mor g _) x) ;
    mor_dir _ x := mor_dir (mor g _) _ (mor_dir (mor f _) _ x) ;
  |} ;
|}.

Definition ε := X.

Definition absurd A: Dual mt A.
Proof.
exists (fun x => x).
cbn.
intros.
eexists.
Unshelve.
2: {
  cbn.
  intros p.
  refine (inr (tt,
   match p with
   | inl mt => match mt with end
   | inr (_, p') => p'
   end)).
}
cbn.
intros [[]|[? p]].
cbn.
apply (fun x => x).
Defined.

Definition nilpotent: Dual (ε * ε) mt.
Proof.
unfold ε.
exists (fun x => K unit + x).
cbn.
intro t.
exists
  (fun q =>
    inr (
    match q with
    | inl _ => (tt, inl tt)
    | inr (_, q) => (tt, inr q)
    end)).
cbn.
intros [?|[? q]].
- cbn.
  intros [b|[]].
  apply (if b then inl tt else inr tt).
- cbn.
  apply (fun x => x).
Defined.

