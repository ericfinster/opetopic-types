{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import MiniUniverse

module Decorations where

  data Decor {ℓ} (X : Set ℓ) : ℙ → Set ℓ where
     null : Decor X ⊥ₚ
     term : (x : X) → Decor X ⊤ₚ
     plus : {U V : ℙ} → Decor X U → Decor X V
       → Decor X (U ⊔ₚ V)
     times : {U : ℙ} {V : El U → ℙ}
       → (ρ : (u : El U) → Decor X (V u))
       → Decor X (Σₚ U V)

  app : ∀ {ℓ} {X : Set ℓ} {U : ℙ}
    → Decor X U → El U → X
  app {X = X} null = ⊥ₚ-elim (λ _ → X)
  app {X = X} (term x) = ⊤ₚ-elim (λ _ → X) x
  app {X = X} (plus DU DV) =
    ⊔ₚ-elim (λ _ → X) (app DU) (app DV)
  app {X = X} (times {U} {V} ρ) =
    Σₚ-elim U V (λ _ → X) (λ u → app (ρ u))

  Decor↓ : ∀ {ℓ ℓ↓} {X : Set ℓ} (X↓ : X → Set ℓ↓)
    → {P : ℙ} → Decor X P → Set ℓ↓
  Decor↓ X↓ null = ⊤
  Decor↓ X↓ (term x) = X↓ x
  Decor↓ X↓ (plus DU DV) =
    Decor↓ X↓ DU × Decor↓ X↓ DV
  Decor↓ X↓ (times {U} {V} ρ) =
    (u : El U) → Decor↓ X↓ (ρ u)

  postulate
  
    app↓ : ∀ {ℓ ℓ↓} {X : Set ℓ} {X↓ : X → Set ℓ↓}
      → {P : ℙ} {D : Decor X P}
      → (D↓ : Decor↓ X↓ D)
      → (p : El P) → X↓ (app D p)
      
  -- -- app↓ X↓ .⊥ₚ null D↓ = {!!}
  -- -- app↓ X↓ .⊤ₚ (term x) D↓ = {!!}
  -- -- app↓ X↓ .(U ⊔ₚ V) (plus {U} {V} DU DV) D↓ = {!!}
  -- -- app↓ X↓ .(Σₚ U V) (times {U} {V} ρ) D↓ = {!!}
