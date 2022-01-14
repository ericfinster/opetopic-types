{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import Opetopes
open import OpetopicType
open import OpetopicMap

module TheUniverse where

  𝕆U : ∀ {ℓ} (n : ℕ) → 𝕆 (ℓ-suc ℓ) n
  𝕆U* : ∀ {ℓ} (n : ℕ) → 𝕆 (ℓ-suc ℓ) n
  𝕦 : ∀ {ℓ} (n : ℕ) → 𝕆U* {ℓ} n ⇒ 𝕆U {ℓ} n

  𝕆U O = tt
  𝕆U {ℓ = ℓ} (S n) = 𝕆U n , λ {o} f →
    (f' : Frm (𝕆U* n) o) (e : Frm⇒ (𝕦 n) f' ≡ f)
    → Set ℓ
  
  𝕆U* O = tt
  𝕆U* {ℓ} (S n) = 𝕆U* n , λ {o} f* →
    Σ ((f' : Frm (𝕆U* n) o) (e : Frm⇒ (𝕦 n) f' ≡ Frm⇒ (𝕦 n) f*) → Set ℓ) (λ F → F f* refl)
  
  𝕦 O = tt
  𝕦 (S n) = 𝕦 n , λ {o} {f} X → fst X
