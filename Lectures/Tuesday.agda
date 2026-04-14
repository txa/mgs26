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

