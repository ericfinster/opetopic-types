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
    Σₚ : (U : ℙ) → πₚ U (cst ℙ) → ℙ
    ⟦_,_⟧ₚ : {U : ℙ} {V : πₚ U (cst ℙ)}
      → (u : El U) (v : El (app V u))
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
    
    π-Σ : ∀ {ℓ} (U : ℙ) (V : πₚ U (cst ℙ))
      → (X : El (Σₚ U V) → Set ℓ)
      -- → πₚ U (λ u → πₚ (app V u) (λ v → X ⟦ u , v ⟧ₚ))
      → (ϕ : (u : El U) → πₚ (app V u) (λ v → X ⟦ u , v ⟧ₚ))
      → πₚ (Σₚ U V) X 

    -- So the only way I can find to escape this infinite loop here is
    -- to actually allow a function type here when introducing a Σ.
    -- Otherwise, we just seem to get stuck in every direction...

    -- Is this a problem?  In priciple, this thing will still need
    -- to be constructed using elminators, so ....

    --
    --  Constant decorations
    --
    
    cstₚ : ∀ {ℓ} {X : Set ℓ} (P : ℙ) (x : X)
      → πₚ P (cst X)

    cst-⊥ : ∀ {ℓ} {X : Set ℓ} (x : X)
      → cstₚ ⊥ₚ x ↦ π-⊥ (cst X)
      
    cst-⊤ : ∀ {ℓ} {X : Set ℓ} (x : X)
      → cstₚ ⊤ₚ x ↦ π-⊤ (cst X) x

    cst-⊔ : ∀ {ℓ} {X : Set ℓ} (x : X)
      → {U V : ℙ}
      → cstₚ (U ⊔ₚ V) x ↦ π-⊔ (cst X) (cstₚ U x) (cstₚ V x)

    cst-Σ : ∀ {ℓ} {X : Set ℓ} (x : X)
      → (U : ℙ) (V : πₚ U (cst ℙ))
      → cstₚ (Σₚ U V) x ↦ π-Σ U V (cst X) (λ u → cstₚ (app V u) x)

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

    fst-π-Σ : ∀ {ℓ ℓ↓} (U : ℙ) (V : πₚ U (cst ℙ))
      → (X : El (Σₚ U V) → Set ℓ)
      → (X↓ : (uv : El (Σₚ U V)) → X uv → Set ℓ↓)
      → (ϕ : (u : El U) → πₚ (app V u) (λ v → Σ (X ⟦ u , v ⟧ₚ) (X↓ ⟦ u , v ⟧ₚ)))
      → fst-π {X = X} {X↓ = X↓} (π-Σ U V _ ϕ) ↦ π-Σ U V X (λ u → fst-π (ϕ u))

    --
    --  More operators
    -- 
    
    Σ↓ₚ : {U : ℙ} {V : πₚ U (cst ℙ)}
      → πₚ (Σₚ U V) (cst ℙ)
      → πₚ U (cst ℙ)

    ⊔↓ₚ : {U : ℙ} 
      → (V : πₚ U (cst ℙ)) (W : πₚ U (cst ℙ))
      → πₚ U (cst ℙ)
      
    --
    --  Laws for Positions
    --

    -- Additive right unit
    ⊔ₚ-unit-r : (U : ℙ)
      → U ⊔ₚ ⊥ₚ ↦ U
    {-# REWRITE ⊔ₚ-unit-r #-}

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
      → Σₚ U (cstₚ U ⊤ₚ) ↦ U
    {-# REWRITE Σₚ-unit-r #-}
    
    -- Multiplicative left unit
    Σₚ-unit-l : (V : πₚ ⊤ₚ (cst ℙ))
      → Σₚ ⊤ₚ V ↦ app V ttₚ
    {-# REWRITE Σₚ-unit-l #-}

    -- Multiplicative left zero
    Σₚ-zero-r : (U : ℙ)
      → Σₚ U (cstₚ U ⊥ₚ) ↦ ⊥ₚ
    {-# REWRITE Σₚ-zero-r #-}

    -- Multiplicative right zero
    Σₚ-zero-l : (V : πₚ ⊥ₚ (cst ℙ))
      → Σₚ ⊥ₚ V ↦ ⊥ₚ
    {-# REWRITE Σₚ-zero-l #-}

    -- Multiplicative associativity
    Σₚ-assoc : (U : ℙ) (V : πₚ U (cst ℙ))
      → (W : πₚ (Σₚ U V) (cst ℙ))
      → Σₚ (Σₚ U V) W ↦ Σₚ U (Σ↓ₚ {V = V} W)
    {-# REWRITE Σₚ-assoc #-}

    -- Right Distributivity
    ⊔ₚ-Σₚ-distrib-r : (U V : ℙ)
      → (W : πₚ U (cst ℙ)) (Z : πₚ V (cst ℙ))
      → Σₚ (U ⊔ₚ V) (π-⊔ (cst ℙ) W Z) ↦ Σₚ U W ⊔ₚ Σₚ V Z
    {-# REWRITE ⊔ₚ-Σₚ-distrib-r #-}

    -- Left Distributivity
    ⊔ₚ-Σₚ-distrib-l : {U : ℙ}
      → (V : πₚ U (cst ℙ)) (W : πₚ U (cst ℙ))
      → Σₚ U (⊔↓ₚ V W) ↦ Σₚ U V ⊔ₚ Σₚ U W
    {-# REWRITE ⊔ₚ-Σₚ-distrib-l #-}
