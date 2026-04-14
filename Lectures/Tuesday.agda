{-
MGS 26 : TT with Agda
Tuesday - The power of dependent types
-}

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ 

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATURAL ℕ #-}

-- What is a dependent type?
-- ℕ : Set
-- Fin : ℕ → Set 
-- A : Set, B : A → Set

data List (A : Set) : Set where 
  [] : List A
  _∷_ : A → List A → List A -- \::

-- List : Set → Set 
-- [] : {A : Set} → List A
-- _∷_ : {A : Set} → ...

variable A B C : Set

snoc : List A → A → List A
snoc [] a = a ∷ []
snoc (b ∷ as) a = b ∷ snoc as a

rev : List A → List A
rev [] = []
rev (a ∷ as) = snoc (rev as) a

infixr 5 _∷_

l123 : List ℕ
l123 = 1 ∷ 2 ∷ 3 ∷ []

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

_!!_ : List A → ℕ → Maybe A
[] !! n = nothing
(x ∷ as) !! zero = just x
(x ∷ as) !! suc n = as !! n

-- Vec A n = Lists of length n

variable l m n : ℕ

data Vec (A : Set) : ℕ → Set where 
  [] : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)

v123 : Vec ℕ 3
v123 =  1 ∷ 2 ∷ 3 ∷ []

snoc-v : Vec A n → A → Vec A (suc n)
snoc-v [] a = a ∷ []
snoc-v (b ∷ as) a = b ∷ snoc-v as a

rev-v : Vec A n → Vec A n
rev-v {n = .zero} [] = []
rev-v {n = .(suc _)} (x ∷ as) = snoc-v (rev-v as) x

{-
Fin 0 = {}
Fin 1 = { 0 }
Fin 2 = { 0 , 1 }
...
Fin (suc n) = { 0 , suc i where i : Fin n}
-}

data Fin : ℕ → Set where
  zero : Fin (suc n)
  suc : Fin n → Fin (suc n)

_!!v_ : Vec A n → Fin n → A
[] !!v ()
(x ∷ as) !!v zero = x
(x ∷ as) !!v suc n = as !!v n

{-
Function types 

A , B : Set
-----------
A → B : Set

A : Set, B : A → Set
--------------------
(x : A) → B x : Set
{x : A} → B x : Set

Π-type, dependent function type
f : (x : A) → B x : Set
a : A
------------------------
f a : B a

f : {x : A} → B x : Set
f {a} : B a
f : B a

A , B : Set
------------
A × B : Set 


a : A, b : B
----------------
a , b : A × B

Σ-type, dependent pair type

A : Set , B : A → Set
---------------------
Σ A B : Set

a : A , b : B a
---------------
a , b : Σ A B

-}

record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- _,_ : {B : A → Set} → (a : A) → B a → Σ A B
-- proj₁ (a , b) = a
-- proj₂ (a , b) = b

data Bool : Set where
  true : Bool
  false : Bool

If : Set → Set → Bool → Set
If A B true = A
If A B false = B

_⊎'_ : Set → Set → Set 
A ⊎' B = Σ Bool (If A B)

_×'_ : Set → Set → Set
A ×' B = (b : Bool) → If A B b



