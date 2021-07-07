{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import MiniUniverse
open import AbsoluteOpetopicTypes
open import DependentOpetopicType
open import OpetopicAlgebra

module TheUniverse where

  --
  --  Infinitely iterating the "fillers" construction ...
  --

  𝕌∞ : ∀ {ℓ} {n : ℕ} (X : 𝕆 (ℓ-suc ℓ) n) (X↓ : 𝕆↓ ℓ X) → 𝕆∞ X
  𝕌•∞ : ∀ {ℓ} {n : ℕ} (X : 𝕆 (ℓ-suc ℓ) n) (X↓ : 𝕆↓ ℓ X) → 𝕆↓∞ (𝕌∞ X X↓) X↓ 
  
  Head (𝕌∞ {ℓ} X X↓) f = (f↓ : Frm↓ X↓ f) → Set ℓ 
  Tail (𝕌∞ {ℓ} X X↓) = 𝕌∞ (X , (λ f → Frm↓ X↓ f → Set ℓ)) (X↓  , λ f↓ R → R f↓)

  Head↓ (𝕌•∞ X X↓) f↓ R = R f↓
  Tail↓ (𝕌•∞ {ℓ} X X↓) = 𝕌•∞ (X , (λ f → Frm↓ X↓ f → Set ℓ)) (X↓  , λ f↓ R → R f↓)

  -- The canonical fibration is multiplicative
  𝕌-mult : ∀ {ℓ} {n : ℕ} (X : 𝕆 (ℓ-suc ℓ) n) (X↓ : 𝕆↓ ℓ X)
    → mult-struct (X , Head (𝕌∞ X X↓)) (Head (Tail (𝕌∞ X X↓)))
  𝕌-mult X X↓ f o ν =
    (λ f↓ → Σ (Opr↓ X↓ f↓ o) (λ o↓ → (p : El (pos o)) → ν p (typ↓ o↓ p))) ,
    (λ { (f↓ , (o↓ , ν↓) , f↓ₛ) → f↓ₛ ≡ ⟪ o↓ , ν↓ ⟫f↓ })

  -- Iterating the previous construction 
  𝕌-Mult∞ : ∀ {ℓ} {n : ℕ} (X : 𝕆 (ℓ-suc ℓ) n) (X↓ : 𝕆↓ ℓ X)
    → Mult∞ (X , Head (𝕌∞ X X↓)) (Tail (𝕌∞ X X↓))
  Mult∞.m (𝕌-Mult∞ X X↓) = 𝕌-mult X X↓ 
  Mult∞.h (𝕌-Mult∞ X X↓) = 𝕌-Mult∞ (X , Head (𝕌∞ X X↓))
                                    (X↓ , λ f↓ R → R f↓)


