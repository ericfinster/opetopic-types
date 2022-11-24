open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType

module Native.OpetopicTerm where

  data 𝕆Term {ℓ ℓ↓} : {n : ℕ} (X : 𝕆Type ℓ n) (X↓ : 𝕆Type↓ ℓ↓ X)
    → Type (ℓ-max ℓ ℓ↓) 

  Frm↑ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
    → (τ : 𝕆Term X X↓)
    → {ο : 𝕆 n} (f : Frm X ο) → Frm↓ X↓ f

  Web↑ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
    → (τ : 𝕆Term X X↓)
    → {ο : 𝕆 n} {f : Frm X ο}
    → {ρ : ℙ ο} (ω : Web X f ρ)
    → Web↓ X↓ (Frm↑ τ f) ω

  postulate

    Shp↓-Web↑ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
      → (τ : 𝕆Term X X↓)
      → {ο : 𝕆 n} {f : Frm X ο}
      → {ρ : ℙ ο} (ω : Web X f ρ)
      → (p : Pos ρ)
      → Shp↓ X↓ (Web↑ τ ω) p ↦ Frm↑ τ (Shp X ω p)
    {-# REWRITE Shp↓-Web↑ #-}

    Web↑-η : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
      → (τ : 𝕆Term X X↓)
      → {ο : 𝕆 n} (f : Frm X ο)
      → Web↑ τ (η X f) ↦ η↓ X↓ (Frm↑ τ f)
    {-# REWRITE Web↑-η #-}

    Web↑-μ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
      → (τ : 𝕆Term X X↓)
      → {ο : 𝕆 n} {f : Frm X ο}
      → {ρ : ℙ ο} (ω : Web X f ρ)
      → {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
      → (ϵ : (p : Pos ρ) → Web X (Shp X ω p) (δ p))
      → Web↑ τ (μ X ω ϵ) ↦ μ↓ X↓ (Web↑ τ ω) λ p → Web↑ τ (ϵ p)
    {-# REWRITE Web↑-μ #-}

  --
  --  Implementation 
  --
  
  {-# NO_UNIVERSE_CHECK #-}
  data 𝕆Term {ℓ ℓ↓} where

    ■ : 𝕆Term ○ ○↓ 

    _►_ : {n : ℕ} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
      → {P : Idx X → Type ℓ}
      → {P↓ : {i : Idx X} → P i → Idx↓ X↓ i → Type ℓ↓} 
      → (τₙ : 𝕆Term X X↓)
      → (τₛₙ : {ο : 𝕆 n} {f : Frm X ο} → (x : P (ο , f)) → P↓ x (Frm↑ τₙ f))
      → 𝕆Term (X ∥ P) (X↓ ∥↓ P↓)

  Frm↑ ■ ● = ●↓
  Frm↑ (τₙ ► τₛₙ) (f ►⟦ t ∣ ρ , ω , δ ⟧) =
    Frm↑ τₙ f ►⟦ τₛₙ t ∣ Web↑ τₙ ω , (λ p → τₛₙ (δ p)) ⟧↓
  
  Web↑ ■ arr = arr↓
  Web↑ (τₙ ► τₛₙ) (lf t) = lf↓ (τₛₙ t)
  Web↑ (τₙ ► τₛₙ) (nd t (ρ , ω , ν) δ) =
    nd↓ (τₛₙ t) (Web↑ τₙ ω , λ p → τₛₙ (ν p))
      (λ p → _ , Web↑ (τₙ ► τₛₙ) (δ p .snd .snd))
