module Core.Prelude where

  --
  --  Sorts and Levels
  --
  
  open import Agda.Primitive public
    using    ( Level )
    renaming ( lzero to ℓ-zero
             ; lsuc  to ℓ-suc
             ; _⊔_   to ℓ-max
             ; Set   to Type
             ; Setω  to Typeω )
  open import Agda.Builtin.Sigma public

  --
  --  Rewriting
  --
  
  infix 10 _↦_
  
  postulate  
    _↦_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ

  {-# BUILTIN REWRITE _↦_ #-}

  --
  --  Sigma Types
  --
  
  open import Agda.Builtin.Sigma public

  -- Σ-types
  infix 2 Σ-syntax

  Σ-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
  Σ-syntax = Σ

  syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

  --
  --  Natural Numbers
  --
  
  open import Agda.Builtin.Nat public
    using (zero; suc)
    renaming (Nat to ℕ)

  --
  --  Level parametric unit type
  --

  record 𝟙 (ℓ : Level) : Type ℓ where
    instance constructor ● 

  --
  --  Useful functions
  --

  infixr 40 _∘_ 

  _∘_ : ∀ {ℓ₀ ℓ₁ ℓ₂} {A : Type ℓ₀} {B : Type ℓ₁} {C : Type ℓ₂}
    → (f : B → C) (g : A → B) → A → C
  (f ∘ g) x = f (g x) 
    
  cst : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    → B → A → B
  cst b _ = b
  
