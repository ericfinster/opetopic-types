--
--  OpetopicType.agda - Definition of Opetopic Types in Context
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Prelude
open import Opetopes
open import OpetopicCtx
open import OpetopicType

module OpetopicTerm where

  𝕆Term : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx ℓ₀ n} (X : 𝕆Type Γ ℓ₁)
    → Type (ℓ-max ℓ₀ ℓ₁)

  Frm-Tm : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx ℓ₀ n} {X : 𝕆Type Γ ℓ₁} (σ : 𝕆Term X)
    → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜) → Frm↓ X f

  {-# TERMINATING #-}
  Cns-Tm : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx ℓ₀ n} {X : 𝕆Type Γ ℓ₁} (σ : 𝕆Term X)
    → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
    → {f : Frm Γ 𝑜} (c : Cns Γ f 𝑝)
    → Cns↓ X (Frm-Tm σ f) c

  postulate

    Shp-Tm : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx ℓ₀ n} {X : 𝕆Type Γ ℓ₁} (σ : 𝕆Term X)
      → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → {f : Frm Γ 𝑜} (c : Cns Γ f 𝑝) (p : Pos 𝑝)
      → Frm-Tm σ (Shp Γ c p) ↦ Shp↓ X (Cns-Tm σ c) p
    {-# REWRITE Shp-Tm #-}

    η-Tm : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx ℓ₀ n} {X : 𝕆Type Γ ℓ₁} (σ : 𝕆Term X)
      → {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
      → Cns-Tm σ (η Γ f) ↦ η↓ X (Frm-Tm σ f)
    {-# REWRITE η-Tm #-}

    μ-Tm : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx ℓ₀ n} {X : 𝕆Type Γ ℓ₁} (σ : 𝕆Term X)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
      → {𝑝 : 𝒫 𝑜} (c : Cns Γ f 𝑝)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → (d : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑞 p))
      → Cns-Tm σ (μ Γ c d) ↦ μ↓ X (Cns-Tm σ c) (λ p → Cns-Tm σ (d p))
    {-# REWRITE μ-Tm #-}

  𝕆Term {zero} X = Lift Unit
  𝕆Term {suc n} {Γ = Γₙ , Γₛₙ} (Xₙ , Xₛₙ) =
    Σ[ xₙ ∈ 𝕆Term Xₙ ]
    ({𝑜 : 𝒪 n} {f : Frm Γₙ 𝑜} (γ : Γₛₙ f) → Xₛₙ (Frm-Tm xₙ f ) γ)

  Frm-Tm {zero} σ f = lift tt
  Frm-Tm {suc n} {X = Xₙ , Xₛₙ} (σₙ , σₛₙ) (f , x , c , y) =
    Frm-Tm σₙ f , σₛₙ x , Cns-Tm σₙ c , λ p → σₛₙ (y p)
  
  Cns-Tm {zero} σ c = lift tt
  Cns-Tm {suc n} (σₙ , σₛₙ) (lf x) = idp
  Cns-Tm {suc n} (σₙ , σₛₙ) (nd x c y d z ψ) =
    Cns-Tm σₙ c , σₛₙ ∘ y , Cns-Tm σₙ ∘ d , (λ p q → σₛₙ (z p q)) ,
      (λ p → Cns-Tm (σₙ , σₛₙ) (ψ p)) , idp



