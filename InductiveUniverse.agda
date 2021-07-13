{-# OPTIONS --without-K --rewriting --type-in-type --no-positivity #-}

open import MiniHoTT

module InductiveUniverse where

  data ℙ : Set

  {-# TERMINATING #-}
  El : ℙ → Set

  data πₚ : (P : ℙ) → (X : El P → Set) → Set 
  app : {P : ℙ} {X : El P → Set}
    → πₚ P X → (p : El P) → X p

  infixr 40 _⊔ₚ_

  data ℙ where
    ⊥ₚ : ℙ
    ⊤ₚ : ℙ
    _⊔ₚ_ : (U : ℙ) → (V : ℙ) → ℙ
    Σₚ : (U : ℙ) (V : πₚ U (cst ℙ)) → ℙ 

  El ⊥ₚ = ∅
  El ⊤ₚ = ⊤
  El (U ⊔ₚ V) = El U ⊔ El V
  El (Σₚ U V) = Σ (El U) (λ u → El (app V u))

  data πₚ where
    π-⊥ : {X : El ⊥ₚ → Set} → πₚ ⊥ₚ X
    π-⊤ : {X : El ⊤ₚ → Set} 
      → X tt → πₚ ⊤ₚ X
    π-⊔ : {U V : ℙ} {X : El (U ⊔ₚ V) → Set}
      → πₚ U (λ u → X (inl u))
      → πₚ V (λ v → X (inr v))
      → πₚ (U ⊔ₚ V) X
    π-Σ : {U : ℙ} {V : πₚ U (cst ℙ)}
      → {X : El (Σₚ U V) → Set}
      → πₚ U (λ u → πₚ (app V u) (λ v → X (u , v)))
      → πₚ (Σₚ U V) X
      
  app (π-⊤ x) tt = x
  app (π-⊔ σ τ) (inl u) = app σ u
  app (π-⊔ σ τ) (inr v) = app τ v
  app (π-Σ σ) (u , v) = app (app σ u) v
