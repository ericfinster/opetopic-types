--
--  OpetopicMap.agda - Maps of opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Unit
open import Cubical.Data.Nat

open import Prelude
open import Opetopes
open import OpetopicCtx

module OpetopicSub where

  infixr 40 _⇒_

  _⇒_ : ∀ {ℓ₀ ℓ₁ n} → 𝕆Ctx ℓ₀ n → 𝕆Ctx ℓ₁ n
    → Type (ℓ-max ℓ₀ ℓ₁)

  Frm⇒ : ∀ {ℓ₀ ℓ₁ n} {Γ : 𝕆Ctx ℓ₀ n} {Δ : 𝕆Ctx ℓ₁ n} (σ : Γ ⇒ Δ)
    → {o : 𝒪 n} → Frm Γ o → Frm Δ o
    
  Cns⇒ : ∀ {ℓ₀ ℓ₁ n} {Γ : 𝕆Ctx ℓ₀ n} {Δ : 𝕆Ctx ℓ₁ n} (σ : Γ ⇒ Δ)
    → {o : 𝒪 n} {ρ : 𝒫 o} {f : Frm Γ o}
    → Cns Γ f ρ → Cns Δ (Frm⇒ σ f) ρ

  postulate

    Shp-Frm⇒ : ∀ {ℓ₀ ℓ₁ n} {Γ : 𝕆Ctx ℓ₀ n} {Δ : 𝕆Ctx ℓ₁ n} (σ : Γ ⇒ Δ)
      → {o : 𝒪 n} {ρ : 𝒫 o} {f : Frm Γ o} (c : Cns Γ f ρ) (p : Pos ρ)
      → Frm⇒ σ (Shp Γ c p) ↦ Shp Δ (Cns⇒ σ c) p
    {-# REWRITE Shp-Frm⇒ #-} 

    η⇒ : ∀ {ℓ₀ ℓ₁ n} {Γ : 𝕆Ctx ℓ₀ n} {Δ : 𝕆Ctx ℓ₁ n} (σ : Γ ⇒ Δ)
      → {o : 𝒪 n} (f : Frm Γ o)
      → Cns⇒ σ (η Γ f) ↦ η Δ (Frm⇒ σ f)
    {-# REWRITE η⇒ #-} 

    μ⇒ : ∀ {ℓ₀ ℓ₁ n} {Γ : 𝕆Ctx ℓ₀ n} {Δ : 𝕆Ctx ℓ₁ n} (σ : Γ ⇒ Δ)
      → {o : 𝒪 n} {f : Frm Γ o}
      → {ρ : 𝒫 o} (c : Cns Γ f ρ)
      → {ι : (p : Pos ρ) → 𝒫 (Typ ρ p)}
      → (κ : (p : Pos ρ) → Cns Γ (Shp Γ c p) (ι p))
      → Cns⇒ σ (μ Γ c κ) ↦ μ Δ (Cns⇒ σ c) (λ p → Cns⇒ σ (κ p))
    {-# REWRITE μ⇒ #-}

  module _ {ℓ₀ ℓ₁ n} {Γₙ : 𝕆Ctx ℓ₀ n} {Δₙ : 𝕆Ctx ℓ₁ n}
           (Γₛₙ : {o : 𝒪 n} → Frm Γₙ o → Type ℓ₀)
           (Δₛₙ : {o : 𝒪 n} → Frm Δₙ o → Type ℓ₁)
           (σₙ : Γₙ ⇒ Δₙ) (σₛₙ : {o : 𝒪 n} {f : Frm Γₙ o} → Γₛₙ f → Δₛₙ (Frm⇒ σₙ f)) where

    WebFrm⇒ : {o : 𝒪 n} {ρ : 𝒫 o}
      → WebFrm Γₙ Γₛₙ ρ → WebFrm Δₙ Δₛₙ ρ 
    WebFrm⇒ (f , x , c , y) = Frm⇒ σₙ f , σₛₙ x , Cns⇒ σₙ c , λ p → σₛₙ (y p) 

    Web⇒ : {o : 𝒪 n} {ρ : 𝒫 o}
      → {φ : WebFrm Γₙ Γₛₙ ρ} {τ : 𝒯r ρ}
      → Web Γₙ Γₛₙ φ τ → Web Δₙ Δₛₙ (WebFrm⇒ φ) τ 
    Web⇒ (lf x) = lf (σₛₙ x)
    Web⇒ (nd x c y d z ψ) =
      nd (σₛₙ x) (Cns⇒ σₙ c) (σₛₙ ∘ y) (Cns⇒ σₙ ∘ d)
         (λ p q → σₛₙ (z p q)) (Web⇒ ∘ ψ) 


  _⇒_ {n = zero} _ _ = Lift Unit
  _⇒_ {n = suc n} (Γₙ , Γₛₙ) (Δₙ , Δₛₙ) =
    Σ (Γₙ ⇒ Δₙ) (λ σ →
     {o : 𝒪 n} {f : Frm Γₙ o}
     → Γₛₙ f → Δₛₙ (Frm⇒ σ f))

  Frm⇒ {n = zero} σ _ = lift tt
  Frm⇒ {n = suc n} {Γₙ , Γₛₙ} {Δₙ , Δₛₙ} (σₙ , σₛₙ) =
    WebFrm⇒ Γₛₙ Δₛₙ σₙ σₛₙ

  Cns⇒ {n = zero} _ _ = lift tt
  Cns⇒ {n = suc n} {Γₙ , Γₛₙ} {Δₙ , Δₛₙ} (σₙ , σₛₙ) =
    Web⇒ Γₛₙ Δₛₙ σₙ σₛₙ
  
  --
  --  Composition
  --

  infixr 30 _⊚_
  
  _⊚_ : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {Γ : 𝕆Ctx ℓ₀ n} {Δ : 𝕆Ctx ℓ₁ n} {Θ : 𝕆Ctx ℓ₂ n}
    → (Δ ⇒ Θ) → (Γ ⇒ Δ) → (Γ ⇒ Θ)

  postulate

    ⊚-Frm : ∀ {ℓ₀ ℓ₁ ℓ₂ n} {Γ : 𝕆Ctx ℓ₀ n} {Δ : 𝕆Ctx ℓ₁ n} {Θ : 𝕆Ctx ℓ₂ n}
      → (σ : Δ ⇒ Θ) (τ : Γ ⇒ Δ) (o : 𝒪 n) (f : Frm Γ o)
      → Frm⇒ (σ ⊚ τ) f ↦ Frm⇒ σ (Frm⇒ τ f)
    {-# REWRITE ⊚-Frm #-}

    ⊚-assoc : ∀ {ℓ₀ ℓ₁ ℓ₂ ℓ₃ n}
      → {Γ : 𝕆Ctx ℓ₀ n} {Δ : 𝕆Ctx ℓ₁ n} {Θ : 𝕆Ctx ℓ₂ n} {W : 𝕆Ctx ℓ₃ n}
      → (σ : Θ ⇒ W) (τ : Δ ⇒ Θ) (γ : Γ ⇒ Δ)
      → (σ ⊚ τ) ⊚ γ ↦ σ ⊚ τ ⊚ γ
    {-# REWRITE ⊚-assoc #-}

    -- And unit laws ...

  _⊚_ {n = zero} σ τ = lift tt
  _⊚_ {n = suc n} {Γₙ , Γₛₙ} {Δₙ , Δₛₙ} {Θₙ , Θₛₙ} (σₙ , σₛₙ) (τₙ , τₛₙ) =
    σₙ ⊚ τₙ , λ x → σₛₙ (τₛₙ x)

