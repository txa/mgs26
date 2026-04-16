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

sym-j : (a b : A) → a ≡ b → b ≡ a 
sym-j a b = J (λ a b _ → b ≡ a) refl

trans-j : (a b c : A) → a ≡ b → b ≡ c → a ≡ c
trans-j a b c = J (λ x y _ → y ≡ c → x ≡ c) (λ zc → zc)

K : (M : (a : A) → a ≡ a → Set) 
  → ({a : A} → M a refl)
  → {a : A} (p : a ≡ a) → M a p
K M mr refl = mr

uip-jk : (a b : A)(p q : a ≡ b) → p ≡ q
uip-jk a b = J (λ a b p → (q : a ≡ b) → p ≡ q)
              (K (λ a pa → refl ≡ pa) (λ {_} → refl))

-- What can prove from J?

-- laws of a groupoid

left-unit : {a b : A}(p : a ≡ b) → trans refl p ≡ p
left-unit p = refl  -- holds definitionally

right-unit : {a b : A}(p : a ≡ b) → trans p refl ≡ p
right-unit refl = refl

left-inv : {a b : A}(p : a ≡ b) → trans (sym p) p ≡ refl
left-inv refl = refl

right-inv : {a b : A}(p : a ≡ b) → trans p (sym p) ≡ refl
right-inv refl = refl

assoc : {a b c d : A}(p : a ≡ b)(q : b ≡ c)(r : c ≡ d)
      → trans (trans p q) r ≡ trans p (trans q r)
assoc refl q r = refl

{-
From J we can prove that equality is a groupoid.

Hofmann: we can construct a model of Type Theory where types
are interpreted as groupoid.
UIP and K are not provable.

ok, lets add K.
=> HoTT , univalence

function extensionality

funext : (f g : A → B) → ((a : A) → f a ≡ g a) → f ≡ g

-}

f g : ℕ → ℕ
f x = x + 0
g x = 0 + x

fxgx : (x : ℕ) → f x ≡ g x
fxgx = {!   !}

fg : f ≡ g
fg = {!   !}

-- P : (A → B) → Set
-- (x : A) → f x ≡ g s
-- P f → P g

-- Leibniz : equality of indescernibles

{-
Setoids = Type + equivalence relation
functions = functions + fun ext 
SETOIDHELL
LICS99 : we can interpret TT using setoids
TT + strict prop

P : SProp
p q : P
----------
p = q

P Q : SProp
P <-> Q -> P ≡ Q 

What is equality of types ?
-}