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

  --
  --  Various Helper Functions
  --
  
  𝕌Src : ∀ {ℓ n} (i : Idx (𝕌 ℓ n)) → Type (ℓ-suc ℓ)
  𝕌Src {ℓ} {n} i = Src (𝕌 ℓ n) 𝕌-cell i 

  𝕍Src : ∀ {ℓ n} {i : Idx (𝕌 ℓ n)} (S : 𝕌Src i) (f↓ : Idx↓ (𝕍 ℓ n) i) → Type ℓ
  𝕍Src {ℓ} {n} S f↓ = Src↓ (𝕍 ℓ n) 𝕍-cell S f↓

  𝕌ret : ∀ {ℓ n} {i : Idx (𝕌 ℓ n)} → 𝕌-cell i → 𝕌Src i
  𝕌ret {ℓ} {n} T = ret (𝕌 ℓ n) 𝕌-cell T 

  𝕍ret : ∀ {ℓ n} {ο : 𝕆 n} {F : Frm (𝕌 ℓ n) ο}
    → (T : 𝕌-cell (ο , F)) {f↓ : Frm↓ (𝕍 ℓ n) F} (t : T f↓)
    → 𝕍Src (ret (𝕌 ℓ n) 𝕌-cell T) f↓
  𝕍ret {ℓ} {n} T t↓ = ret↓ (𝕍 ℓ n) 𝕍-cell {t = T} t↓
