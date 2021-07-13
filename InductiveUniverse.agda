{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

open import MiniHoTT

module InductiveUniverse where

  infixr 40 _⊔ₚ_

  postulate
  
    ℙ : Set
    El : ℙ → Set

  data πₚ : (P : ℙ) → (X : El P → Set) → Set 
  app : {P : ℙ} {X : El P → Set}
    → πₚ P X → (p : El P) → X p

  postulate

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

  data πₚ where
    π-⊥ : {X : El ⊥ₚ → Set} → πₚ ⊥ₚ X
    π-⊤ : {X : El ⊤ₚ → Set} 
      → X ttₚ → πₚ ⊤ₚ X
    π-⊔ : {U V : ℙ} {X : El (U ⊔ₚ V) → Set}
      → πₚ U (λ u → X (inlₚ u))
      → πₚ V (λ v → X (inrₚ v))
      → πₚ (U ⊔ₚ V) X
    π-Σ : {U : ℙ} {V : πₚ U (cst ℙ)}
      → {X : El (Σₚ U V) → Set}
      → πₚ U (λ u → πₚ (app V u) (λ v → X ⟦ u , v ⟧ₚ))
      → πₚ (Σₚ U V) X
      
  app π-⊥ = {!!}
  app (π-⊤ x) = {!!}
  app (π-⊔ σ τ) = {!!}
  app (π-Σ σ) = {!!}

  -- Interesting.  So app can't even be defined by recursion,
  -- since we would need to actually have the eliminators.
  -- But app *is* this eliminator.  So the best we can do
  -- is say how it computes on *canonical elements*, which
  -- is what we would do for the eliminator.

  -- But then this isn't so intersting ...

