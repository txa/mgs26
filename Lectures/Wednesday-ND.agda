{-
MGS 26 : TT with Agda
Wednesday - Dependent types in logic
-}

-- prelude 

postulate String : Set
{-# BUILTIN STRING String #-}

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

¬_ : Set → Set
¬ P = P → ⊥

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

-- Minimal logic (natural deduction)

data Form : Set where
    Atom : String → Form
    _[→]_ : Form → Form → Form

data Con : Set where
    • : Con 
    _,_ : Con → Form → Con

infixr 10 _[→]_
infix 5 _⊢_ -- \vdash

variable Γ Δ : Con
variable φ ψ θ : Form -- \phi , \psi , \theta

data _⊢_ : Con → Form → Set where
           ---------
    zero : Γ , φ ⊢ φ

    suc : Γ ⊢ φ → 
          ---------
          Γ , ψ ⊢ φ

    lam : Γ , φ ⊢ ψ →
          -----------
          Γ ⊢ φ [→] ψ

    app : Γ ⊢ φ [→] ψ →
          Γ ⊢ φ →
          -------------
          Γ ⊢ ψ

-- S : (A → B → C) → (A → B) → (A → C)
-- S = λ f → λ g → λ a → (f a) (g a)

S-d : • ⊢ (Atom "P" [→] Atom "Q" [→] Atom "R") [→] 
            (Atom "P" [→] Atom "Q") [→] (Atom "P" [→] Atom "R")
S-d = lam (lam (lam (app (app (suc (suc zero)) zero) 
      (app (suc zero) zero))))

---

-- noproof : ¬ (• ⊢ (Atom "P" [→] Atom "Q") [→] Atom "P")
-- noproof (lam (suc d)) = {!   !}
-- noproof (lam (app d d₁)) = {!   !}
-- noproof (app d d₁) = {!   !}


--- 

Env : Set₁
Env = String → Set

my-env : Env
my-env "P" = ⊥
my-env "Q" = ⊤
my-env _ = ⊥

⟦_⟧F : Form → Env → Set
⟦ Atom x ⟧F ρ = ρ x
⟦ φ [→] ψ ⟧F ρ = (⟦ φ ⟧F ρ) → (⟦ ψ ⟧F ρ)

⟦_⟧C : Con → Env → Set
⟦ • ⟧C ρ = ⊤
⟦ Γ , φ ⟧C ρ = ⟦ Γ ⟧C ρ ∧ ⟦ φ ⟧F ρ

sound : Γ ⊢ φ → (ρ : Env) → ⟦ Γ ⟧C ρ → ⟦ φ ⟧F ρ
sound zero ρ (_ , x) = x
sound (suc d) ρ (γ , _) = sound d ρ γ
sound (lam d) ρ γ x = sound d ρ (γ , x)
sound (app d e) ρ γ = sound d ρ γ (sound e ρ γ)
-- (P → Q) → P

noproof : ¬ (• ⊢ (Atom "P" [→] Atom "Q") [→] Atom "P")
noproof d = sound d my-env tt λ x → tt
-- Pierce formula ?
-- ((P → Q) → P) → P

P-F : Form
P-F = ((Atom "P" [→] Atom "Q") [→] Atom "P") [→] Atom "P"

no-pierce : ¬ (• ⊢ P-F)
no-pierce = {!!}
-- Kripke
