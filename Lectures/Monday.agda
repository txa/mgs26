{-
MGS 26 : TT with Agda
Monday - Intro

https://github.com/txa/mgs26

What is Type Theory?
- TT is functional programming language
  with a very powerful static type system
- TT is a logical system using propositions as types
  (Prop = Type, Proof = program) also Curry-Howard equivalence
- TT is an alternative foundation of Mathematics
  alternative ZFC a ∈ A , a : A
-}

-- prove that + is associative

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

-- C-c C-l check buffer
one = suc zero
two = suc one

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n) 

-- C-c C-, : show context
-- C-c C-c : split patterns
-- C-c C-SPC : open shed
{-# BUILTIN NATURAL ℕ #-}

-- (l + m) + n ≡ l + (m + n)
data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

infix 4 _≡_

variable A B C : Set

cong : (f : A → B) → {a b : A} → a ≡ b → f a ≡ f b
cong f (refl {a = a}) = refl {a = f a}

assoc : (l m n : ℕ) → (l + m) + n ≡ l + (m + n)
assoc zero m n = refl {a = m + n}
assoc (suc l) m n = cong suc (assoc l m n)
