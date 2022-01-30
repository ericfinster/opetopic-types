--
--  Elements.agda - experimenting with elements
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Prelude
open import Opetopes
open import OpetopicCtx
open import OpetopicType

module Elements where

  El : ∀ {n ℓ} (Γ : 𝕆Ctx n ℓ) → Type ℓ
  
  Frm-El : ∀ {n ℓ} {Γ : 𝕆Ctx n ℓ} (σ : El Γ)
    → (o : 𝒪 n) → Frm Γ o

  {-# TERMINATING #-}
  Cns-El : ∀ {n ℓ} {Γ : 𝕆Ctx n ℓ} (σ : El Γ)
    → {o : 𝒪 n} (ρ : 𝒫 o)
    → Cns Γ (Frm-El σ o) ρ 

  postulate

    Shp-Frm-Cns : ∀ {ℓ n} (Γ : 𝕆Ctx n ℓ) (σ : El Γ)
      → {o : 𝒪 n} (ρ : 𝒫 o) (p : Pos ρ)
      → Frm-El σ (Typ ρ p) ↦ Shp Γ (Cns-El σ ρ) p 
    {-# REWRITE Shp-Frm-Cns #-}

    η-El : ∀ {ℓ n} (Γ : 𝕆Ctx n ℓ) (σ : El Γ)
      → (o : 𝒪 n)
      → Cns-El σ (ηₒ o) ↦ η Γ (Frm-El σ o) 
    {-# REWRITE η-El #-}

    μ-El : ∀ {n ℓ} (Γ : 𝕆Ctx n ℓ) (σ : El Γ)
      → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} 
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → Cns-El σ (μₒ (𝑝 , 𝑞)) ↦ μ Γ (Cns-El σ 𝑝) (λ p → Cns-El σ (𝑞 p)) 
    {-# REWRITE μ-El #-}

  El {zero} Γ = Lift Unit
  El {suc n} (Γₙ , Γₛₙ) =
    Σ (El Γₙ) (λ σ → (o : 𝒪 n) → Γₛₙ (Frm-El σ o))

  Frm-El {zero} σ o = lift tt
  Frm-El {suc n} {Γ = Γₙ , Γₛₙ} (σₙ , σₛₙ) (o , ρ) =
    (Frm-El σₙ o  , σₛₙ o , Cns-El σₙ ρ , (λ p → σₛₙ (Typ ρ p)))

  Cns-El {zero} σ ρ = lift tt
  Cns-El {suc n} (σₙ , σₛₙ) {𝑜 , ._} lfₒ = lf (σₛₙ 𝑜)
  Cns-El {suc n} (σₙ , σₛₙ) {𝑜 , ._} (ndₒ (𝑝 , 𝑞) 𝑟) =
    nd (σₛₙ 𝑜) (Cns-El σₙ 𝑝) (λ p → σₛₙ (Typ 𝑝 p))
       (λ p → Cns-El σₙ (𝑞 p)) (λ p q → σₛₙ (Typ (𝑞 p) q))
       (λ p → Cns-El (σₙ , σₛₙ) (𝑟 p))

  --
  --  Now, can we extract the fiber at an element?
  --

  fiber-at : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx n ℓ₀} (σ : El Γ)
    → 𝕆Type Γ ℓ₁ → 𝕆Ctx n ℓ₁

  postulate
  
    frm-ovr : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx n ℓ₀} (σ : El Γ)
      → (X : 𝕆Type Γ ℓ₁)
      → {𝑜 : 𝒪 n} (f : Frm (fiber-at σ X) 𝑜)
      → Frm↓ X (Frm-El σ 𝑜)

  fiber-at {zero} σ X = lift tt
  fiber-at {suc n} (σₙ , σₛₙ) (Xₙ , Xₛₙ) =
    fiber-at σₙ Xₙ , λ {𝑜} f → Xₛₙ (frm-ovr σₙ Xₙ f) (σₛₙ 𝑜)


  --
  --  Okay, and so can you make these do things?
  --

  Σₒ : ∀ {n ℓ₀ ℓ₁} (Γ : 𝕆Ctx n ℓ₀) (X : 𝕆Type Γ ℓ₁)
    → 𝕆Ctx n (ℓ-max ℓ₀ ℓ₁)

  prₒ : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx n ℓ₀} {X : 𝕆Type Γ ℓ₁}
    → (γ : El Γ) (x : El (fiber-at γ X))
    → El (Σₒ Γ X)

  data ΣCell {n ℓ₀ ℓ₁} (Γ : 𝕆Ctx (suc n) ℓ₀) (X : 𝕆Type Γ ℓ₁)
    : {𝑜 : 𝒪 n} → Frm (Σₒ (fst Γ) (fst X)) 𝑜 → Type (ℓ-max ℓ₀ ℓ₁) where

    pair : (γ : El (Γ)) (x : El (fiber-at γ X))
      → (𝑜 : 𝒪 n) → ΣCell Γ X (Frm-El (prₒ (fst γ) (fst x)) 𝑜) 

  Σₒ {zero} Γ X = lift tt
  Σₒ {suc n} (Γₙ , Γₛₙ) (Xₙ , Xₛₙ) =
    Σₒ Γₙ Xₙ  , ΣCell (Γₙ , Γₛₙ) (Xₙ , Xₛₙ)

  prₒ {zero} γ x = lift tt
  prₒ {suc n} γ x = prₒ (fst γ) (fst x) , pair γ x
