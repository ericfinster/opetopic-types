open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType

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
