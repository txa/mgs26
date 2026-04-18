{-# OPTIONS --cubical --guardedness --type-in-type #-}
open import Cubical.Core.Everything hiding (isEquiv ; _≃_)
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

{-
Voevodsky univalence

Cohen , Coquand, Huber, Moertberg
A constructive interpretation of the univalence axiom

I : Set
Interval [0,1]

i0 , i1 : I

a, b : A
p : a ≡ b

p : I → A, p i0 = a, p i1 = b
equality as a path
-}

variable A B C : Set

refl' : (a : A) → a ≡ a
refl' a i = a

{-
~ : I → I -- ~ x = 1-x
~ i0 = i1
~ i1 = i0
-}

sym' : (a b : A)(ab : a ≡ b) → b ≡ a
sym' a b ab i = ab (~ i)

-- funext

funext : (f g : A → B) → ((a : A) → f a ≡ g a) → f ≡ g
funext f g h i a = h a i
{-
h : A → I → B
h a i0 = f a
h a i1 = g a

k = funext h = k i a = h a i
k : I → A → B
k i0 = f
k i1 = g

-}



{-
transp : (A : I → Set)(r : I)(a : A i0) → A i1

if r = i1 then A has to be constant, A i0 = A i1
transp A i1 a = a

r = i0
-}

-- transitivity

trans : (a b c : A) → a ≡ b → b ≡ c → a ≡ c
trans a b c ab bc = transp (λ i → a ≡ bc i) i0 ab
-- A i = a ≡ bc i
-- A i0 = a ≡ b
-- A i1 = a ≡ c

subst' : (a : A)(P : A → Set) → P a → (b : A) → a ≡ b → P b
subst' a P pa b ab = transp (λ i → P (ab i)) i0 pa

-- _∧_ : I → I → I
-- i0 ∧ i = i0
-- i ∧ i0 = i0
-- i1 ∧ i = i
-- i ∧ i1 = i

J' : (a : A)(P : (x : A) → a ≡ x → Set)
         → P a (refl' a)
         → (b : A)(ab : a ≡ b) → P b ab
J' a P pa b ab = transp (λ i → P (ab i) (λ j → ab (i ∧ j))) i0 pa 
-- ? : a ≡ ab i
-- A j → ab (i ∧ j)
-- A i0 = ab i0 = a = refl' a
-- A i1 = ab i
-- if j=0 then i ∧ j = i0, since ab i0 = a
-- if j=1 then i ∧ j = i , since ab i

J'β : (a : A)(P : (x : A) → a ≡ x → Set)(pa : P a (refl' a))
    → J' a P pa a (refl' a) ≡ pa
J'β a P pa i = transp (λ j → P a (refl' a)) i pa
-- i = i0 : J' a P pa a = transp (λ j → P a (refl' a)) i pa
-- i = i1 : transp (λ j → P a (refl' a)) i pa = p1

-- all constants compute, in particular transp computes
-- hcomp : fills higher dimensional cubes
-- cubical doc and CCHM 

is-contr : Set → Set
is-contr A = Σ A (λ a → (b : A) → a ≡ b)

is-prop : Set → Set
is-prop A = (a b : A) → a ≡ b

is-set : Set → Set
is-set A = (a b : A) → is-prop (a ≡ b)

is-of-hlevel : ℕ → Set → Set
is-of-hlevel zero    A = is-contr A
is-of-hlevel (suc n) A = (a b : A) → is-of-hlevel n (a ≡ b)

{-
H-levels (homotopy levels / truncation levels):

  is-contr  =  h-level -2  (contractible: unique up to path)
  is-prop   =  h-level -1  (at most one element up to path)
  is-set    =  h-level  0  (paths between elements are unique)
  ...

if a type has a decidable equality => set, Michael Hebderg
has a stable equality (¬ ¬ (a ≡ b) → a ≡ b)
Set : Gpd 
-}


record Stream (A : Set) : Set where
  constructor _∷_
  coinductive
  field
    hd : A
    tl : Stream A

open Stream

from : ℕ → Stream ℕ
hd (from n) = n
tl (from n) = from (suc n)

-- variable A B C : Set

mapStream : (A → B) → Stream A → Stream B
hd (mapStream f as) = f (hd as)
tl (mapStream f as) = mapStream f (tl as)

lemma : (n : ℕ) → mapStream suc (from n) ≡ from (suc n)
hd (lemma n i) = suc n
tl (lemma n i) = lemma (suc n) i

coind : (R : Stream A → Stream A → Set)
        (isBisim : {as bs : Stream A} → R as bs →
                    (hd as ≡ hd bs) × (R (tl as) (tl bs)))
        → {as bs : Stream A} → R as bs → as ≡ bs
hd (coind R isBisim r i) = fst (isBisim r) i
tl (coind R isBisim r i) = coind R isBisim (snd (isBisim r)) i

-- Quotients = HITs Higher Inductive Types

data ℤ : Set where
  zero : ℤ
  suc : ℤ → ℤ
  prd : ℤ → ℤ
  ps : (x : ℤ) → prd (suc x) ≡ x
  sp : (x : ℤ) → suc (prd x) ≡ x
-- need to truncate
-- isSet : (x y : 𝐙)(p q : x ≡ y) → p ≡ q

_+ℤ_ : ℤ → ℤ → ℤ
zero +ℤ y = y
suc x +ℤ y = suc (x +ℤ y)
prd x +ℤ y = prd (x +ℤ y)
ps x i +ℤ y = ps (x +ℤ y) i
sp x i +ℤ y = sp (x +ℤ y) i

-- geometric object = the circle S¹

data S¹ : Set where
  base : S¹
  loop : base ≡ base

thm : (base ≡ base) ≡ ℤ
thm = {!!} 


record is-iso (φ : A → B) : Set where
  field
    ψ : B → A
    ψφ : (a : A) → ψ (φ a) ≡ a
    φψ : (b : B) → φ (ψ b) ≡ b

record _≅_ (A B : Set) : Set where
  field
    φ : A → B
    iso : is-iso φ

record isEquiv (φ : A → B) : Set where
  field
    ψ : B → A
    ψφ : (a : A) → ψ (φ a) ≡ a
    φψ : (b : B) → φ (ψ b) ≡ b
    φψφ : (a : A) → φψ (φ a) ≡ cong φ (ψφ a) 

record _≃_ (A B : Set) : Set where
  field
    φ : A → B
    equ : isEquiv φ

refl≃ : (A ≃ A)
refl≃ = record { φ = λ x → x ;
                 equ = record { ψ = λ x → x ; ψφ = λ a → refl ;
                       φψ = λ b → refl  ;
                       φψφ = λ a → refl } }

≡→equiv : (A ≡ B) → (A ≃ B)
≡→equiv {A} AB = subst (λ X → A ≃ X) AB refl≃

-- univalence axiom (need to add levels, I just assumed Set : Set
ua : isEquiv (≡→equiv {A} {B})
ua = {!!}

{-
Higher Observational Type Theory HOTT
Narya

-}