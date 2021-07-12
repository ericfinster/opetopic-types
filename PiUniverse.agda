{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

module PiUniverse where

  --
  --  A relatively complete picture of a π-finite approach....
  --
  
  postulate

    ℙ : Set
    El : ℙ → Set

    πₚ : ∀ {ℓ} (P : ℙ) (X : El P → Set ℓ) → Set ℓ 
    app : ∀ {ℓ} {P : ℙ} {X : El P → Set ℓ}
      → πₚ P X → (p : El P) → X p

    ⊥ₚ : ℙ

    ⊤ₚ : ℙ
    ttₚ : El ⊤ₚ

    _⊔ₚ_ : ℙ → ℙ → ℙ
    inlₚ : {U V : ℙ} → El U → El (U ⊔ₚ V)
    inrₚ : {U V : ℙ} → El V → El (U ⊔ₚ V)
    
    Σₚ : (U : ℙ) → πₚ U (cst ℙ) → ℙ
    ⟦_,_⟧ₚ : {U : ℙ} {V : πₚ U (cst ℙ)}
      → (u : El U) (v : El (app V u))
      → El (Σₚ U V) 

    π-⊥ : ∀ {ℓ} (X : El ⊥ₚ → Set ℓ)
      → πₚ ⊥ₚ X
      
    π-⊤ : ∀ {ℓ} (X : El ⊤ₚ → Set ℓ)
      (x : X ttₚ) → πₚ ⊤ₚ X

    π-⊔ : ∀ {ℓ} {U V : ℙ} (X : El (U ⊔ₚ V) → Set ℓ)
      → πₚ U (λ u → X (inlₚ u))
      → πₚ V (λ v → X (inrₚ v))
      → πₚ (U ⊔ₚ V) X 
    
    π-Σ : ∀ {ℓ} (U : ℙ) (V : πₚ U (cst ℙ))
      → (X : El (Σₚ U V) → Set ℓ)
      → πₚ U (λ u → πₚ (app V u) (λ v → X ⟦ u , v ⟧ₚ))
      → πₚ (Σₚ U V) X 

