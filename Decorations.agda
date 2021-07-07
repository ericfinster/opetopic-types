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
       
  app : ∀ {ℓ} (X : Set ℓ) (U : ℙ)
    → Decor X U → El U → X
  app X .⊥ₚ null = ⊥ₚ-elim (λ _ → X)
  app X .⊤ₚ (term x) = ⊤ₚ-elim (λ _ → X) x
  app X .(U ⊔ₚ V) (plus {U} {V} DU DV) =
    ⊔ₚ-elim (λ _ → X) (app X U DU) (app X V DV)
  app X .(Σₚ U V) (times {U} {V} ρ) =
    Σₚ-elim U V (λ _ → X) (λ u → app X (V u) (ρ u))
