open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType

module Native.Weakening where

  Wk : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆Type ℓ₀ n) (Y : 𝕆Type ℓ₁ n)
    → 𝕆Type↓ ℓ₁ X

  πFrm : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆Type ℓ₀ n) (Y : 𝕆Type ℓ₁ n)
    → {ο : 𝕆 n} {f : Frm X ο}
    → Frm↓ (Wk X Y) f → Frm Y ο 

  πWeb : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆Type ℓ₀ n) (Y : 𝕆Type ℓ₁ n)
    → {ο : 𝕆 n} {ρ : ℙ ο}
    → {f : Frm X ο} {ω : Web X f ρ}
    → {f↓ : Frm↓ (Wk X Y) f}
    → (ω↓ : Web↓ (Wk X Y) f↓ ω)
    → Web Y (πFrm X Y f↓) ρ 

  πIdx : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆Type ℓ₀ n) (Y : 𝕆Type ℓ₁ n)
    → {i : Idx X} (i↓ : Idx↓ (Wk X Y) i)
    → Idx Y
  πIdx X Y {ο , f} f↓ = (ο , πFrm X Y f↓)

  postulate

    Shp-πWeb : ∀ {ℓ₀ ℓ₁ n} (X : 𝕆Type ℓ₀ n) (Y : 𝕆Type ℓ₁ n)
      → {ο : 𝕆 n} {ρ : ℙ ο}
      → {f : Frm X ο} {ω : Web X f ρ}
      → {f↓ : Frm↓ (Wk X Y) f}
      → (ω↓ : Web↓ (Wk X Y) f↓ ω)
      → (p : Pos ρ)
      → Shp Y (πWeb X Y ω↓) p ↦ πFrm X Y (Shp↓ (Wk X Y) ω↓ p)
    {-# REWRITE Shp-πWeb #-} 

    πWeb-η : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} (Y : 𝕆Type ℓ₁ n)
      → {ο : 𝕆 n} {f : Frm X ο} (f↓ : Frm↓ (Wk X Y) f)
      → πWeb X Y (η↓ (Wk X Y) f↓) ↦ η Y (πFrm X Y f↓)
    {-# REWRITE πWeb-η #-}

  -- μ↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
  --   → {ο : 𝕆 n} {f : Frm X ο} {f↓ : Frm↓ X↓ f}
  --   → {ρ : ℙ ο} {ω : Web X f ρ} (ω↓ : Web↓ X↓ f↓ ω)
  --   → {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
  --   → {ϵ : (p : Pos ρ) → Web X (Shp X ω p) (δ p)}
  --   → (ϵ↓ : (p : Pos ρ) → Web↓ X↓ (Shp↓ X↓ ω↓ p) (ϵ p))
  --   → Web↓ X↓ f↓ (μ X ω ϵ)

  Wk ○ ○ = ○↓
  Wk (X ∥ P) (Y ∥ Q) =
    Wk X Y ∥↓ λ _ i↓ → Q (πIdx X Y i↓)

  πFrm ○ ○ ●↓ = ●
  πFrm (X ∥ P) (Y ∥ Q) {f = f ►⟦ t ∣ s ⟧} (f↓ ►⟦ t↓ ∣ s↓ ⟧↓) =
    πFrm X Y f↓ ►⟦ t↓ ∣ s .fst , (πWeb X Y (s↓ .fst)) , (λ p → s↓ .snd p) ⟧

  πWeb ○ ○ arr↓ = arr
  πWeb (X ∥ P) (Y ∥ Q) (lf↓ t↓) = lf t↓
  πWeb (X ∥ P) (Y ∥ Q) (nd↓ t↓ s↓ δ↓) = {!!}
