{-
MGS 26 : TT with Agda
Monday - Exercises

-}

--- from the lecture
data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ 

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATURAL ℕ #-}

data _≡_ {A : Set} : A → A → Set where
    refl : {a : A} → a ≡ a

infix 4 _≡_

variable A B C : Set

cong : (f : A → B){a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl

assoc : (l m n : ℕ) → l + (m + n) ≡ (l + m) + n
assoc zero m n = refl 
assoc (suc l) m n = cong suc (assoc l m n)
---
lneutr : (n : ℕ) → 0 + n ≡ n
lneutr = {!   !}

rneutr : (n : ℕ) → n + 0 ≡ n
rneutr = {!   !}

comm : (m n : ℕ) → m + n ≡ n + m
comm = {!   !}

{-
Additional exercise

define _*_ and prove that (ℕ,0,+,1,*) is a commutative semiring

-}

