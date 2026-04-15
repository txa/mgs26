{-
MGS 26 : TT with Agda
Wednesday - Dependent types in logic
-}

-- Prelude

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ 

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

data _≡_ {A : Set} : A → A → Set where
    refl : {a : A} → a ≡ a

variable A B C : Set

cong : (f : A → B){a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl

infix 4 _≡_

data ⊥ : Set where

¬_ : Set → Set
¬ P = P → ⊥

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _∧_

infix 0 _↔_
_↔_ : Set → Set → Set
P ↔ Q = (P → Q) ∧ (Q → P)

{-# BUILTIN NATURAL ℕ #-}

variable l m n : ℕ

-- Start here!

data _≤_ : ℕ → ℕ → Set where
    le-0 : 0 ≤ n
    le-S : m ≤ n → suc m ≤ suc n

2≤3 : 2 ≤ 3
2≤3 = le-S (le-S le-0) -- C-c C-r

¬3≤2 : ¬ (3 ≤ 2)
¬3≤2 (le-S (le-S ()))

-- what are the properties of _≤_
-- trans , refl, anti-symmetry

refl≤ : n ≤ n
refl≤ {zero} = le-0
refl≤ {suc n} = le-S (refl≤ {n})

trans≤ : l ≤ m → m ≤ n → l ≤ n
trans≤ le-0 q = le-0
trans≤ (le-S p) (le-S q) = le-S (trans≤ p q)

anti-sym≤ : m ≤ n → n ≤ m → m ≡ n
anti-sym≤ le-0 le-0 = refl
anti-sym≤ (le-S p) (le-S q) = cong suc (anti-sym≤ p q)

--- Exercise starts here!

-- here is another definition of ≤
-- show that they are equivalent
data _≤'_ : ℕ → ℕ → Set where
  refl≤' : m ≤' m
  le'-S : m ≤' n → m ≤' suc n

thm : m ≤ n ↔ m ≤' n
thm = {!   !}

-- Prove that _≤_ is decidable.

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : ¬ A → Dec A

_≤?_ : (m n : ℕ) → Dec (m ≤ n)
_≤?_ = {!   !}

-- Extra exercise : Prove that the PIerce formula is not derivable.