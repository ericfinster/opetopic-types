open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType

module Native.DependentOpetopicType where

  --
  --  Signature 
  --
  
  data 𝕆Type↓ {ℓ} (ℓ↓ : Level)
    : {n : ℕ} → 𝕆Type ℓ n → Type (ℓ-suc ℓ↓)

  data Frm↓ {ℓ ℓ↓} : {n : ℕ} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {ο : 𝕆 n} (f : Frm X ο) → Type ℓ↓

  data Web↓ {ℓ ℓ↓} : {n : ℕ} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {ο : 𝕆 n} {f : Frm X ο} (f↓ : Frm↓ X↓ f)
    → {ρ : ℙ ο} (ω : Web X f ρ) → Type ℓ↓

  Shp↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {ο : 𝕆 n} {f : Frm X ο} {f↓ : Frm↓ X↓ f}
    → {ρ : ℙ ο} {ω : Web X f ρ} (ω↓ : Web↓ X↓ f↓ ω)
    → (p : Pos ρ) → Frm↓ X↓ (Shp X ω p)

  --
  --  Monadic Structure
  --

  η↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {ο : 𝕆 n} {f : Frm X ο} (f↓ : Frm↓ X↓ f)
    → Web↓ X↓ f↓ (η X f)
    
  μ↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
    → {ο : 𝕆 n} {f : Frm X ο} {f↓ : Frm↓ X↓ f}
    → {ρ : ℙ ο} {ω : Web X f ρ} (ω↓ : Web↓ X↓ f↓ ω)
    → {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
    → {ϵ : (p : Pos ρ) → Web X (Shp X ω p) (δ p)}
    → (ϵ↓ : (p : Pos ρ) → Web↓ X↓ (Shp↓ X↓ ω↓ p) (ϵ p))
    → Web↓ X↓ f↓ (μ X ω ϵ)

  --
  --  Equations 
  --

  postulate

    Shp↓-η↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
      → {ο : 𝕆 n} {f : Frm X ο} (f↓ : Frm↓ X↓ f)
      → (p : Pos (ηₒ ο))
      → Shp↓ X↓ (η↓ X↓ f↓) p ↦ f↓
    {-# REWRITE Shp↓-η↓ #-}
    
    Shp↓-μ↓ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
      → {ο : 𝕆 n} {f : Frm X ο} (f↓ : Frm↓ X↓ f)
      → {ρ : ℙ ο} {ω : Web X f ρ} (ω↓ : Web↓ X↓ f↓ ω)
      → {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
      → {ϵ : (p : Pos ρ) → Web X (Shp X ω p) (δ p)}
      → (ϵ↓ : (p : Pos ρ) → Web↓ X↓ (Shp↓ X↓ ω↓ p) (ϵ p))
      → (p : Pos (μₒ ρ δ))
      → Shp↓ X↓ (μ↓ X↓ ω↓ ϵ↓) p ↦ Shp↓ X↓ (ϵ↓ (fstₒ ρ δ p)) (sndₒ ρ δ p) 
    {-# REWRITE Shp↓-μ↓ #-} 

    --
    --  Monadic Laws
    --
    
    μ↓-unit-r : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
      → {ο : 𝕆 n} {f : Frm X ο} (f↓ : Frm↓ X↓ f)
      → {ρ : ℙ ο} {ω : Web X f ρ} (ω↓ : Web↓ X↓ f↓ ω)
      → μ↓ X↓ ω↓ (λ p → η↓ X↓ (Shp↓ X↓ ω↓ p)) ↦ ω↓
    {-# REWRITE μ↓-unit-r #-}
    
    μ↓-unit-l : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
      → {ο : 𝕆 n} {f : Frm X ο} (f↓ : Frm↓ X↓ f)
      → {δ : (p : Pos (ηₒ ο)) → ℙ ο}
      → {ϵ : (p : Pos (ηₒ ο)) → Web X (Shp X (η X f) p) (δ p)}
      → (ϵ↓ : (p : Pos (ηₒ ο)) → Web↓ X↓ (Shp↓ X↓ (η↓ X↓ f↓) p) (ϵ p))
      → μ↓ X↓ (η↓ X↓ f↓) ϵ↓ ↦ ϵ↓ (η-posₒ ο) 
    {-# REWRITE μ↓-unit-l #-}

    μ↓-assoc : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} (X↓ : 𝕆Type↓ ℓ↓ X)
      → {ο : 𝕆 n} {f : Frm X ο} (f↓ : Frm↓ X↓ f)
      → {ρ : ℙ ο} {ω : Web X f ρ} (ω↓ : Web↓ X↓ f↓ ω)
      → {δ : (p : Pos ρ) → ℙ (Typ ρ p)}
      → {ϵ : (p : Pos ρ) → Web X (Shp X ω p) (δ p)}
      → (ϵ↓ : (p : Pos ρ) → Web↓ X↓ (Shp↓ X↓ ω↓ p) (ϵ p))
      → {ϕ : (p : Pos (μₒ ρ δ)) → ℙ (Typ (μₒ ρ δ) p)}
      → {ψ : (p : Pos (μₒ ρ δ)) → Web X (Shp X (μ X ω ϵ) p) (ϕ p)}
      → (ψ↓ : (p : Pos (μₒ ρ δ)) → Web↓ X↓ (Shp↓ X↓ (μ↓ X↓ ω↓ ϵ↓) p) (ψ p))
      → μ↓ X↓ (μ↓ X↓ ω↓ ϵ↓) ψ↓ ↦ μ↓ X↓ ω↓ (λ p → μ↓ X↓ (ϵ↓ p) (λ q → ψ↓ (pairₒ ρ δ p q)))
    {-# REWRITE μ↓-assoc #-}

  --
  --  Implementations
  --
  
  {-# NO_UNIVERSE_CHECK #-}
  data 𝕆Type↓ {ℓ} ℓ↓ where

  {-# NO_UNIVERSE_CHECK #-}
  data Frm↓ {ℓ} {ℓ↓} where

  {-# NO_UNIVERSE_CHECK #-}
  data Web↓ {ℓ} {ℓ↓} where 

  Shp↓ = {!!} 

  η↓ = {!!} 
  μ↓ = {!!} 
