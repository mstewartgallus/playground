{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Level

record Monoid (s : Level) : Set (suc s) where
  constructor monoid
  field
    M : Set s
    e : M
    _·_ : M → M → M
    LeftId : ( x : M ) → e · x ≡ x
    RightId : ( x : M ) → x · e ≡ x
    Assoc : ( x y z : M ) → x · (y · z) ≡ (x · y) · z
open Monoid public

record Mon {s p : Level} (A : Monoid s) (B : Monoid p) : Set (s ⊔ p) where
  constructor mon
  field
    op : M A → M B
    HomE : op (e A) ≡ e B
    -- I'm not experienced with Agda
    HomApp : (x y : M A) → op (_·_ A x y) ≡ _·_ B (op x) (op y)

UnitMon : {s : Level} → Monoid s
M UnitMon = Unit*
e UnitMon = tt*
_·_ UnitMon _ _ = tt*
LeftId UnitMon x = _
RightId UnitMon x = _
Assoc UnitMon x y z = _

-- Smash product
data _⊕_ {s p} (A : Monoid s) (B : Monoid p) : Set (s ⊔ p) where
  inl : M A → A ⊕ B
  inr : M B → A ⊕ B
  -- FIXME figure out quotients
  -- smash : inl (e A) ≡ inr (e B)

Sum : {s p : Level} → Monoid s → Monoid p → Monoid (s ⊔ p)
M (Sum A B) = A ⊕ B
e (Sum A B) = inl (e A)
_·_ (Sum A B) (inl a) (inl b) = inl (_·_ A a b)
_·_ (Sum A B) (inr a) (inr b) = inr (_·_ B a b)
_·_ (Sum A B) _ _ = inl (e A)
LeftId (Sum A B) x = _
RightId (Sum A B) x = _
Assoc (Sum A B) x y z = _

-- Just like the standard library Data.Container.Core
-- But Monoids !
infix 5 _▹_
record Container (s p : Level) : Set (suc (s ⊔ p)) where
  constructor _▹_
  field
    Shape : Set s
    Position : Shape → Monoid p
open Container public

record Mor {s p : Level} (A B : Container s p) : Set (suc (s ⊔ p)) where
   constructor mor
   field
     Shape : Shape A → Shape B
     Position : ( x : Container.Shape A ) → Mon (Position B (Shape x)) (Position A x)

_∘_ : {s p : Level} → {A B C : Container s p} → Mor B C → Mor A B → Mor A C
Mor.Shape (f ∘ g) x = Mor.Shape f (Mor.Shape g x)
Mon.op (Mor.Position (f ∘ g) x) y = Mon.op (Mor.Position g x) (Mon.op (Mor.Position f (Mor.Shape g x)) y)
Mon.HomE (Mor.Position (f ∘ g) x) = _
Mon.HomApp (Mor.Position (f ∘ g) x) = _

-- Not sure here, doesn't seem right to me ~ X right ?
UnitCon : {s p : Level} → Container s p
Shape UnitCon = Unit*
Position UnitCon _ = UnitMon

! : {s p : Level} → {A : Container s p} → Mor A UnitCon
Mor.Shape ! _ = tt*
-- Confused here
Mon.op (Mor.Position ! x) y = _
Mon.HomE (Mor.Position ! x) y = _
Mon.HomApp (Mor.Position ! x) y = _

X : {s p : Level} → Container s p
Shape X = Unit*
Position X _ = UnitMon

_*_ : {s p : Level} → Container s p → Container s p → Container s p
Shape (A * B) = Shape A × Shape B
Position (A * B) (a , b) = Sum (Position A a) (Position B b)

<_,_> : {s p : Level} → { C A B : Container s p } → Mor C A → Mor C B → Mor C (A * B)
Mor.Shape (< f , g >) x = (Mor.Shape f x , Mor.Shape g x)
Mon.op (Mor.Position (< f , g >) x) (inl y) = Mon.op (Mor.Position f x) y
Mon.op (Mor.Position (< f , g >) x) (inr y) = Mon.op (Mor.Position g x) y
Mon.HomE (Mor.Position (< f , g >) x) = _
Mon.HomApp (Mor.Position (< f , g >) x) = _

-- Ugly not sure how to do better
record ContainerMonoid (s p : Level) : Set (suc (s ⊔ p)) where
  field
    M : Container s p
    e : Mor UnitCon M
    app : Mor (M * M) M
    LeftId : {A : Container s p} → ( x y : Mor A M ) → app ∘ < e ∘ ! , x > ≡ x
    RightId : {A : Container s p} → ( x y : Mor A M ) → app ∘ < x , e ∘ ! > ≡ x
    Assoc : {A : Container s p} → ( x y z : Mor A M ) →
      app ∘ < x , app ∘ < y , z > > ≡ app ∘ < app ∘ < x , y > , z >

record Fiber {s p : Level} (poly : ContainerMonoid s p) : Set (s ⊔ p)
μ : {s p : Level} → ContainerMonoid s p → Monoid (s ⊔ p)

record Fiber poly where
  inductive
  constructor fiber
  field
    Tag : Shape (ContainerMonoid.M poly)
    Field : Mon (Position (ContainerMonoid.M poly) Tag) (μ poly)

M (μ poly) = Fiber poly
e (μ poly) = fiber
  (Mor.Shape (ContainerMonoid.e poly) tt*)
  (mon (λ _ → e (μ poly)) _ _)
_·_ (μ poly) a b = fiber
  (Mor.Shape (ContainerMonoid.app poly) (Fiber.Tag a , Fiber.Tag b))
  (mon (λ x → _
    ) _ _)
LeftId (μ poly) x = _
RightId (μ poly) x = _
Assoc (μ poly) x y z = _
