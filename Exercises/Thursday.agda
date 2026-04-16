{-
MGS 26 : TT with Agda
Thursday - The mystery of equality

Conor McBride

In politics and in Type Theory
the question of equality 
is highly controversial.
-}

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n) 

-- inductive "definition" of equality
data _≡_ {A : Set} : A → A → Set where
    refl : {a : A} → a ≡ a

infix 4 _≡_

variable A B C : Set

cong : (f : A → B){a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl

sym : {a b : A} → a ≡ b → b ≡ a 
sym refl = refl

trans : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q

---

uip : {a b : A}(p q : a ≡ b) → p ≡ q 
uip refl refl = refl

J : (M : (a b : A) → a ≡ b → Set) 
  → ({a : A} → M a a refl)
  → {a b : A} (p : a ≡ b) → M a b p
J M mr refl = mr 

K : (M : (a : A) → a ≡ a → Set) 
  → ({a : A} → M a refl)
  → {a : A} (p : a ≡ a) → M a p
K M mr refl = mr

-- solutions

sym-j : (a b : A) → a ≡ b → b ≡ a
sym-j a b = {!   !}

trans-j : (a b c : A) → a ≡ b → b ≡ c → a ≡ c
trans-j a b c = {!   !}

uip-jk : (a b : A)(p q : a ≡ b) → p ≡ q
uip-jk a b = {!   !}

-- What can prove from J?

-- laws of a groupoid

left-unit : {a b : A}(p : a ≡ b) → trans refl p ≡ p
left-unit p = {!   !}

right-unit : {a b : A}(p : a ≡ b) → trans p refl ≡ p
right-unit p = {!   !}

left-inv : {a b : A}(p : a ≡ b) → trans (sym p) p ≡ refl
left-inv p = {!   !}

right-inv : {a b : A}(p : a ≡ b) → trans p (sym p) ≡ refl
right-inv p = {!   !}

assoc : {a b c d : A}(p : a ≡ b)(q : b ≡ c)(r : c ≡ d)
      → trans (trans p q) r ≡ trans p (trans q r)
assoc p q r = {!   !}

left-unit-j : (a b : A)(p : a ≡ b) → trans refl p ≡ p
left-unit-j a b = {!   !}

right-unit-j : (a b : A)(p : a ≡ b) → trans p refl ≡ p
right-unit-j a b = {!   !}

left-inv-j : (a b : A)(p : a ≡ b) → trans (sym p) p ≡ refl
left-inv-j a b = {!   !}

right-inv-j : (a b : A)(p : a ≡ b) → trans p (sym p) ≡ refl
right-inv-j a b = {!   !}

assoc-j : (a b : A)(p : a ≡ b)(c d : A)(q : b ≡ c)(r : c ≡ d)
        → trans (trans p q) r ≡ trans p (trans q r)
assoc-j a b p c d = {!   !}
