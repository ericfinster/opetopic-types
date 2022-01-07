{-# OPTIONS --without-K --rewriting --no-positivity-check #-}

open import MiniHoTT
open import Opetopes

module OpetopicType where

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  Frm : ∀ {ℓ n} (X : 𝕆 ℓ n) → 𝒪 n → Set ℓ
  Pd : ∀ {ℓ n} (X : 𝕆 ℓ n) {o : 𝒪 n} (f : Frm X o) (τ : 𝒯r o) → Set ℓ 

  𝕆 ℓ O = Set ℓ
  𝕆 ℓ (S n) =
    Σ (𝕆 ℓ n) (λ Xₙ →
      (o : 𝒪 n) (f : Frm Xₙ o) → Set ℓ)
  
  Frm X ● = ⊤
  Frm (Xₙ , Xₛₙ) (o ▸ τ) =
    Σ (Frm Xₙ o) (λ f →
      Pd Xₙ f τ × Xₛₙ o f)

  Pd X f τ = {!!} 
