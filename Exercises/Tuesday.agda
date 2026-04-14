{-
MGS 26 : TT with Agda
Tuesday - Exercises

Complete the definitions 
and check the test cases using C-c C-n testi
-}

-- From the lecture

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ 

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATURAL ℕ #-}

data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A

infixr 5 _∷_

variable A B C : Set
variable l m n : ℕ

data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _∷_ : A → Vec A n → Vec A (suc n)

data Fin : ℕ → Set where
  zero : Fin (suc n)
  suc : Fin n → Fin (suc n)

--- 

-- functions on Fin

-- max computes the maximal element in each Fin n
max : Fin (suc n)
max = {!   !}

test1 : Fin 4
test1 = max {3}
-- suc (suc (suc zero))

-- emb embeds Fin n into Fin (suc n) without adding one
emb : Fin n → Fin (suc n)
emb = {!   !}

test2 : Fin 4
test2 = emb {3} (suc zero)

-- inv maps Fin n to Fin n reversing the order of elements
inv : Fin n → Fin n
inv = {!   !}

test3 : Fin 4
test3 = inv {4} (suc zero)
-- transposing a matrix 

Matrix : ℕ → ℕ → Set {- Matrix m n is an m x n Matrix -}
Matrix m n = Vec (Vec ℕ n) m

m33 : Matrix 3 3
m33 = (1 ∷ 2 ∷ 3 ∷ []) 
    ∷ (4 ∷ 5 ∷ 6 ∷ []) 
    ∷ (7 ∷ 8 ∷ 9 ∷ []) 
    ∷ []

m32 : Matrix 3 2
m32 = (1 ∷ 2 ∷ []) 
    ∷ (4 ∷ 5 ∷ []) 
    ∷ (7 ∷ 8 ∷ []) 
    ∷ []


transpose : Matrix m n → Matrix n m
transpose = {!   !}

test4 : Matrix 2 3
test4 = transpose m32
{-
(1 ∷ 4 ∷ 7 ∷ []) ∷ 
(2 ∷ 5 ∷ 8 ∷ []) ∷ []
-}

test5 : Matrix 3 3
test5 = transpose m33
{-
(1 ∷ 4 ∷ 7 ∷ []) ∷ 
(2 ∷ 5 ∷ 8 ∷ []) ∷ 
(3 ∷ 6 ∷ 9 ∷ []) ∷ []
-}