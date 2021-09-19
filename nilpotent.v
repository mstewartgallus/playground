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

Module Import Mor.
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

  Definition id A: Mor A A := {|
    mor_pos x := x ;
    mor_dir _ y := y ;
  |}.

  Definition compose {A B C} (f: Mor B C) (g: Mor A B): Mor A C := {|
    mor_pos x := mor_pos f (mor_pos g x) ;
    mor_dir _ x := mor_dir g _ (mor_dir f _ x) ;
  |}.

  Definition bang A: Mor A (K unit) := {|
    mor_pos _ := tt : pos (K unit) ;
    mor_dir _ x := match x with end ;
  |}.

  Definition fanout {A B C} (f: Mor C A) (g: Mor C B): Mor C (A * B) :=
  {|
    mor_pos x := (mor_pos f x, mor_pos g x) : pos (A * B) ;
    mor_dir x xy := match xy with
     | inl s => mor_dir f x s
     | inr t => mor_dir g x t
     end ;
  |}.
 
  Definition fst {A B}: Mor (A * B) A :=
  {|
    mor_pos (x: pos (A * B)) := fst x ;
    mor_dir _ x := inl x ;
  |}.
  Definition snd {A B}: Mor (A * B) B :=
  {|
    mor_pos (x: pos (A * B)) := snd x ;
    mor_dir _ x := inr x ;
  |}.

  Definition absurd A: Mor mt A := {|
    mor_pos (x: pos mt) := match x with end ;
    mor_dir x := match x with end ;
  |}.

 Definition fanin {A B C} (f: Mor A C) (g: Mor B C): Mor (A + B) C :=
  {|
    mor_pos (xy: pos (A + B)) :=
      match xy with
      | inl x => mor_pos f x
      | inr x => mor_pos g x
      end ;
    mor_dir xy :=
      match xy with
      | inl x => mor_dir f x
      | inr x => mor_dir g x
      end ;
  |}.
 
  Definition inl {A B}: Mor A (A + B) :=
  {|
    mor_pos x := inl x : pos (A + B) ;
    mor_dir _ x := x ;
  |}.
  Definition inr {A B}: Mor B (A + B) :=
  {|
    mor_pos x := inr x : pos (A + B) ;
    mor_dir _ x := x ;
  |}.
  
End Mor.

(* quotient by mapping to the presheaf of poly some t, p + X^2 * t *)
Record Dual (P Q: Poly) := {
  ix: Poly -> Poly ;
  mor t: Mor (P + X2 * t) (Q + X2 * ix t);
}.
Arguments ix {P Q}.
Arguments mor {P Q}.

Definition id A: Dual A A := {|
  ix P := P ;
  mor _ := id _ ;
|}.

Definition compose {A B C} (f: Dual B C) (g: Dual A B): Dual A C := {|
  ix P := ix f (ix g P) ;
  mor _ := compose (mor f _) (mor g _) ;
|}.

Definition ε := X.

Definition map {A B} (f: Mor A B): Dual A B.
Proof.
exists (fun x => x).
intros.
apply fanin.
- apply (Mor.compose inl f).
- apply inr.
Defined.



(* WRONG product *)

Definition nilpotent: Dual (ε * ε) mt.
Proof.
unfold ε.
exists (fun x => K unit + x).
cbn.
intro t.
apply (Mor.compose inr).
apply fanin.
- apply fanout.
  + exists (fun _ => tt).
    cbn.
    intros ? [|].
    * left.
      apply tt.
   * right.
     apply tt.
  + apply (Mor.compose inl).
    apply bang.
- apply fanout.
  + apply fst.
  + apply (Mor.compose inr).
    apply snd.
Defined.
