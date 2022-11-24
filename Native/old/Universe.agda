{-# OPTIONS --cubical #-}

open import Core.Prelude hiding (Σ-syntax)
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType

open import Cubical.Foundations.Everything

module Native.Universe where

  𝒰 : (ℓ : Level) (n : ℕ) → 𝕆Type (ℓ-suc ℓ) n
  𝒱 : (ℓ : Level) (n : ℕ) → 𝕆Type↓ ℓ (𝒰 ℓ n)

  𝒰-cell : ∀ {ℓ n} → Idx (𝒰 ℓ n) → Type (ℓ-suc ℓ)
  𝒰-cell {ℓ} {n} i = (i↓ : Idx↓ (𝒱 ℓ n) i) → Type ℓ 

  𝒱-cell : ∀ {ℓ n} {i : Idx (𝒰 ℓ n)}
    → 𝒰-cell i → Idx↓ (𝒱 ℓ n) i → Type ℓ
  𝒱-cell P f↓ = P f↓ 

  𝒰 ℓ zero = ○
  𝒰 ℓ (suc n) = 𝒰 ℓ n ∥ 𝒰-cell
  
  𝒱 ℓ zero = ○↓
  𝒱 ℓ (suc n) = 𝒱 ℓ n ∥↓ 𝒱-cell

  --  Here's what it means to be fibrant.
  is-fibrant-cell : ∀ {ℓ n} (i : Idx (𝒰 ℓ (suc n)))
    → 𝒰-cell i → Type ℓ
  is-fibrant-cell {ℓ} {n} (._ , f ►⟦ t ∣ s ⟧) P =
    (f↓ : Frm↓ (𝒱  ℓ n) f) (s↓ : Src↓ (𝒱 ℓ n) 𝒱-cell s f↓)
     → isContr (Σ[ t↓ ∈ t f↓ ] (P (f↓ ►⟦ t↓ ∣ s↓ ⟧↓)))

  -- Can we define the subuniverse of fibrant cells w/o Σₒ?
  -- 𝒮 : (ℓ : Level) (n : ℕ) → 𝕆Type (ℓ-suc ℓ) n
  -- 𝒮 ℓ zero = ○
  -- 𝒮 ℓ (suc n) = 𝒮 ℓ n ∥ λ i → {!!}

  -- Yeah, that's what I thought.  This is kind of a problem.
  -- I need a way to simultaneously define the map.
