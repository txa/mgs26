{-
MGS 26 : TT with Agda
Monday - Exercises

-}

--- from the lecture
data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ 

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥ 


data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A

zs : Maybe ℕ → ℕ
zs nothing = zero
zs (just n) = suc n

pred : ℕ → Maybe ℕ
pred zero = nothing
pred (suc n) = just n

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

infix 5 _+_

{-# BUILTIN NATURAL ℕ #-}

data _≡_ {A : Set} : A → A → Set where
    refl : {a : A} → a ≡ a

infix 4 _≡_

no-conf : (n : ℕ) → ¬ (zero ≡ suc n)
no-conf n ()

inj-suc : (m n : ℕ) → suc m ≡ suc n → m ≡ n
inj-suc m .m refl = refl

variable A B C : Set

cong : (f : A → B){a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl

sym : {a b : A} → a ≡ b → b ≡ a 
sym refl = refl

trans : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q

assoc : (l m n : ℕ) → l + (m + n) ≡ (l + m) + n
assoc zero m n = refl 
assoc (suc l) m n = cong suc (assoc l m n)
---
lneutr : (n : ℕ) → 0 + n ≡ n
lneutr n = refl

rneutr : (n : ℕ) → n + 0 ≡ n
rneutr zero = refl
rneutr (suc n) = cong suc (rneutr n)

suc-plus : (m n : ℕ) → suc (n + m) ≡ (n + suc m)
suc-plus m zero = refl
suc-plus m (suc n) = cong suc (suc-plus m n) 
-- C-c C-r

comm : (m n : ℕ) → m + n ≡ n + m
comm zero n = sym (rneutr n)
comm (suc m) n = trans (cong suc (comm m n)) (suc-plus m n)

-- (ℕ , _+_, 0) is a commutative monoid

infix 6 _*_

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + m * n

assoc-* : (l m n : ℕ) → l * (m * n) ≡ (l * m) * n
assoc-* = {!   !}

lneutr-* : (n : ℕ) → 1 * n ≡ n
lneutr-* = {!   !}

rneutr-* : (n : ℕ) → n * 1 ≡ n
rneutr-* = {!   !}

comm-* : (m n : ℕ) → m * n ≡ n * m
comm-* = {!   !}

distr-l : (l m n : ℕ) → (l + m) * n ≡ l * n + m * n
distr-l = {!   !}

{-
Additional exercise

define _*_ and prove that (ℕ,0,+,1,*) is a commutative semiring

(ℕ , _*_ , 1)  is a commutative monoid

-}

record Monoid : Set₁ where
    field 
      X : Set
      e : X
      _o_ : X → X → X
      rneutrX : (x : X) → x o e ≡ x
      lneutrX : (x : X) → e o x ≡ x
      assocX : (x y z : X) → x o (y o z) ≡ (x o y) o z

open Monoid

mon-plus : Monoid
X mon-plus = ℕ
e mon-plus = zero
_o_ mon-plus = _+_
lneutrX mon-plus = lneutr
rneutrX mon-plus = rneutr
assocX mon-plus = assoc