open import Core.Prelude 
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType

module Native.Universe where

  -- The universe together with it's canonical fibration
  𝕌 : (ℓ : Level) (n : ℕ) → 𝕆Type (ℓ-suc ℓ) n
  𝕍 : (ℓ : Level) (n : ℕ) → 𝕆Type↓ ℓ (𝕌 ℓ n)

  𝕌-cell : ∀ {ℓ n} → Idx (𝕌 ℓ n) → Type (ℓ-suc ℓ)
  𝕌-cell {ℓ} {n} i = (i↓ : Idx↓ (𝕍 ℓ n) i) → Type ℓ 

  𝕍-cell : ∀ {ℓ n} {i : Idx (𝕌 ℓ n)}
    → 𝕌-cell i → Idx↓ (𝕍 ℓ n) i → Type ℓ
  𝕍-cell P f↓ = P f↓ 

  𝕌 ℓ zero = ○
  𝕌 ℓ (suc n) = 𝕌 ℓ n ∥ 𝕌-cell
  
  𝕍 ℓ zero = ○↓
  𝕍 ℓ (suc n) = 𝕍 ℓ n ∥↓ 𝕍-cell

