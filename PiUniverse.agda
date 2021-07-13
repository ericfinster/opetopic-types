{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

module PiUniverse where

  infixr 40 _⊔ₚ_

  postulate

    ℙ : Set
    El : ℙ → Set

    -- Small π types and application
    πₚ : ∀ {ℓ} (P : ℙ) (X : El P → Set ℓ) → Set ℓ
    app : ∀ {ℓ} {P : ℙ} {X : El P → Set ℓ}
      → πₚ P X → (p : El P) → X p

    -- Empty
    ⊥ₚ : ℙ

    -- Unit
    ⊤ₚ : ℙ
    ttₚ : El ⊤ₚ

    -- Binary sum
    _⊔ₚ_ : ℙ → ℙ → ℙ
    inlₚ : {U V : ℙ} → El U → El (U ⊔ₚ V)
    inrₚ : {U V : ℙ} → El V → El (U ⊔ₚ V)

    -- Binary multiplication 
    Σₚ : (U : ℙ) (V : El U → ℙ ) → ℙ
    ⟦_,_∣_,_⟧ₚ : (U : ℙ) (V : El U → ℙ)
      → (u : El U) (v : El (V u))
      → El (Σₚ U V) 

    --
    --  Small eliminators
    --
    
    π-⊥ : ∀ {ℓ} (X : El ⊥ₚ → Set ℓ)
      → πₚ ⊥ₚ X
      
    π-⊤ : ∀ {ℓ} (X : El ⊤ₚ → Set ℓ)
      (x : X ttₚ) → πₚ ⊤ₚ X

    π-⊔ : ∀ {ℓ} {U V : ℙ} (X : El (U ⊔ₚ V) → Set ℓ)
      → πₚ U (λ u → X (inlₚ u))
      → πₚ V (λ v → X (inrₚ v))
      → πₚ (U ⊔ₚ V) X 
    
    π-Σ : ∀ {ℓ} (U : ℙ) (V : El U → ℙ)
      → (X : El (Σₚ U V) → Set ℓ)
      → (ϕ : (u : El U) → πₚ (V u) (λ v → X ⟦ U , V ∣ u , v ⟧ₚ))
      → πₚ (Σₚ U V) X 

    --
    --  Definition of App
    --

    app-⊤ : ∀ {ℓ} {X : El ⊤ₚ → Set ℓ} {x : X ttₚ}
      → app (π-⊤ X x) ttₚ ↦ x

    app-⊔-inl : ∀ {ℓ} {U V : ℙ} (X : El (U ⊔ₚ V) → Set ℓ)
      → (σl : πₚ U (λ u → X (inlₚ u)))
      → (σr : πₚ V (λ v → X (inrₚ v)))
      → (u : El U)
      → app (π-⊔ X σl σr) (inlₚ u) ↦ app σl u

    app-⊔-inr : ∀ {ℓ} {U V : ℙ} (X : El (U ⊔ₚ V) → Set ℓ)
      → (σl : πₚ U (λ u → X (inlₚ u)))
      → (σr : πₚ V (λ v → X (inrₚ v)))
      → (v : El V)
      → app (π-⊔ X σl σr) (inrₚ v) ↦ app σr v

    app-Σ : ∀ {ℓ} (U : ℙ) (V : El U → ℙ)
      → (X : El (Σₚ U V) → Set ℓ)
      → (ϕ : (u : El U) → πₚ (V u) (λ v → X ⟦ U , V ∣ u , v ⟧ₚ))
      → (u : El U) (v : El (V u))
      → app (π-Σ U V X ϕ) ⟦ U , V ∣ u , v ⟧ₚ ↦ app (ϕ u) v

    --
    --  First projection  (these could really go in the Sigma module ...)
    --

    fst-π : ∀ {ℓ ℓ↓} {P : ℙ} {X : El P → Set ℓ}
      → {X↓ : (p : El P) → X p → Set ℓ↓} 
      → πₚ P (λ p → Σ (X p) (X↓ p))
      → πₚ P X

    fst-π-⊥ : ∀ {ℓ ℓ↓} {X : El ⊥ₚ → Set ℓ}
      → {X↓ : (b : El ⊥ₚ) → X b → Set ℓ↓}
      → (σ : πₚ ⊥ₚ (λ b → Σ (X b) (X↓ b)))
      → fst-π σ ↦ π-⊥ X 

    fst-π-⊤ : ∀ {ℓ ℓ↓} {X : El ⊤ₚ → Set ℓ}
      → {X↓ : (b : El ⊤ₚ) → X b → Set ℓ↓}
      → (σ : πₚ ⊤ₚ (λ b → Σ (X b) (X↓ b)))
      → fst-π σ ↦ π-⊤ X (fst (app σ ttₚ))

    fst-π-⊔ : ∀ {ℓ ℓ↓} {U V : ℙ} {X : El (U ⊔ₚ V) → Set ℓ}
      → {X↓ : (uv : El (U ⊔ₚ V)) → X uv → Set ℓ↓}
      → (σl : πₚ U (λ u → Σ (X (inlₚ u)) (X↓ (inlₚ u))))
      → (σr : πₚ V (λ v → Σ (X (inrₚ v)) (X↓ (inrₚ v))))
      → fst-π (π-⊔ (λ uv → Σ (X uv) (X↓ uv)) σl σr) ↦
          π-⊔ X (fst-π σl) (fst-π σr)

    fst-π-Σ : ∀ {ℓ ℓ↓} (U : ℙ) (V : El U → ℙ)
      → (X : El (Σₚ U V) → Set ℓ)
      → (X↓ : (uv : El (Σₚ U V)) → X uv → Set ℓ↓)
      → (ϕ : (u : El U) → πₚ (V u) (λ v → Σ (X ⟦ U , V ∣ u , v ⟧ₚ) (X↓ ⟦ U , V ∣ u , v ⟧ₚ)))
      → fst-π {X = X} {X↓ = X↓} (π-Σ U V _ ϕ) ↦ π-Σ U V X (λ u → fst-π (ϕ u))
      
    --
    --  Laws for Positions
    --

    -- Additive right unit
    ⊔ₚ-unit-r : (U : ℙ)
      → U ⊔ₚ ⊥ₚ ↦ U
    {-# REWRITE ⊔ₚ-unit-r #-}

    ⊔ₚ-unit-r-intro : (U : ℙ) (u : El U)
      → inlₚ {V = ⊥ₚ} u ↦ u 
    {-# REWRITE ⊔ₚ-unit-r-intro #-}

    ⊔ₚ-unit-r-π : ∀ {ℓ} {U : ℙ}
      → (X : El (U ⊔ₚ ⊥ₚ) → Set ℓ)
      → (σl : πₚ U (λ u → X (inlₚ {V = ⊥ₚ} u)))
      → (σr : πₚ ⊥ₚ (λ b → X (inrₚ {U = U} b)))
      → π-⊔ X σl σr ↦ σl
    {-# REWRITE ⊔ₚ-unit-r-π #-}

    -- Additive left unit
    ⊔ₚ-unit-l : (V : ℙ)
      → ⊥ₚ ⊔ₚ V ↦ V
    {-# REWRITE ⊔ₚ-unit-l #-}

    -- Additive associativity
    ⊔ₚ-assoc : (U V W : ℙ)
      → (U ⊔ₚ V) ⊔ₚ W ↦ U ⊔ₚ V ⊔ₚ W
    {-# REWRITE ⊔ₚ-assoc #-}

    -- Multiplicative right unit
    Σₚ-unit-r : (U : ℙ)
      → Σₚ U (cst ⊤ₚ) ↦ U
    {-# REWRITE Σₚ-unit-r #-}
    
    -- Multiplicative left unit
    Σₚ-unit-l : (V : El ⊤ₚ → ℙ)
      → Σₚ ⊤ₚ V ↦ V ttₚ
    {-# REWRITE Σₚ-unit-l #-}

    -- Multiplicative left zero
    Σₚ-zero-r : (U : ℙ)
      → Σₚ U (cst ⊥ₚ) ↦ ⊥ₚ
    {-# REWRITE Σₚ-zero-r #-}

    -- Multiplicative right zero
    Σₚ-zero-l : (V : El ⊥ₚ → ℙ)
      → Σₚ ⊥ₚ V ↦ ⊥ₚ
    {-# REWRITE Σₚ-zero-l #-}

    -- Multiplicative associativity
    Σₚ-assoc : (U : ℙ) (V : El U → ℙ)
      → (W : El (Σₚ U V) → ℙ)
      → Σₚ (Σₚ U V) W ↦ Σₚ U (λ u → Σₚ (V u) (λ v → W ⟦ U , V ∣ u , v ⟧ₚ))
    {-# REWRITE Σₚ-assoc #-}

    -- Right Distributivity
    ⊔ₚ-Σₚ-distrib-r : (U V : ℙ)
      → (W : El (U ⊔ₚ V) → ℙ)
      → Σₚ (U ⊔ₚ V) W ↦ Σₚ U (λ u → W (inlₚ {V = V} u)) ⊔ₚ Σₚ V (λ v → W (inrₚ {U = U} v))
    {-# REWRITE ⊔ₚ-Σₚ-distrib-r #-}

    -- Left Distributivity
    ⊔ₚ-Σₚ-distrib-l : {U : ℙ}
      → (V : El U → ℙ) (W : El U → ℙ)
      → Σₚ U (λ u → V u ⊔ₚ W u) ↦ Σₚ U V ⊔ₚ Σₚ U W
    {-# REWRITE ⊔ₚ-Σₚ-distrib-l #-}
