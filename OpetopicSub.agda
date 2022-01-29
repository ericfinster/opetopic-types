--
--  OpetopicMap.agda - Maps of opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Unit
open import Cubical.Data.Nat

open import Prelude
open import Opetopes
open import OpetopicCtx
open import OpetopicType

module OpetopicSub where

  infixr 40 _⇒_

  _⇒_ : ∀ {n ℓ₀ ℓ₁} → 𝕆Ctx n ℓ₀ → 𝕆Ctx n ℓ₁
    → Type (ℓ-max ℓ₀ ℓ₁)

  Frm⇒ : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx n ℓ₀} {Δ : 𝕆Ctx n ℓ₁} (σ : Γ ⇒ Δ)
    → {o : 𝒪 n} → Frm Γ o → Frm Δ o
    
  Cns⇒ : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx n ℓ₀} {Δ : 𝕆Ctx n ℓ₁} (σ : Γ ⇒ Δ)
    → {o : 𝒪 n} {ρ : 𝒫 o} {f : Frm Γ o}
    → Cns Γ f ρ → Cns Δ (Frm⇒ σ f) ρ

  postulate

    Shp-Frm⇒ : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx n ℓ₀} {Δ : 𝕆Ctx n ℓ₁} (σ : Γ ⇒ Δ)
      → {o : 𝒪 n} {ρ : 𝒫 o} {f : Frm Γ o} (c : Cns Γ f ρ) (p : Pos ρ)
      → Frm⇒ σ (Shp Γ c p) ↦ Shp Δ (Cns⇒ σ c) p
    {-# REWRITE Shp-Frm⇒ #-} 

    η⇒ : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx n ℓ₀} {Δ : 𝕆Ctx n ℓ₁} (σ : Γ ⇒ Δ)
      → {o : 𝒪 n} (f : Frm Γ o)
      → Cns⇒ σ (η Γ f) ↦ η Δ (Frm⇒ σ f)
    {-# REWRITE η⇒ #-} 

    μ⇒ : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Ctx n ℓ₀} {Δ : 𝕆Ctx n ℓ₁} (σ : Γ ⇒ Δ)
      → {o : 𝒪 n} {f : Frm Γ o}
      → {ρ : 𝒫 o} (c : Cns Γ f ρ)
      → {ι : (p : Pos ρ) → 𝒫 (Typ ρ p)}
      → (κ : (p : Pos ρ) → Cns Γ (Shp Γ c p) (ι p))
      → Cns⇒ σ (μ Γ c κ) ↦ μ Δ (Cns⇒ σ c) (λ p → Cns⇒ σ (κ p))
    {-# REWRITE μ⇒ #-}

  module _ {n ℓ₀ ℓ₁} {Γₙ : 𝕆Ctx n ℓ₀} {Δₙ : 𝕆Ctx n ℓ₁}
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


  _⇒_ {zero} _ _ = Lift Unit
  _⇒_ {suc n} (Γₙ , Γₛₙ) (Δₙ , Δₛₙ) =
    Σ (Γₙ ⇒ Δₙ) (λ σ →
     {o : 𝒪 n} {f : Frm Γₙ o}
     → Γₛₙ f → Δₛₙ (Frm⇒ σ f))

  Frm⇒ {zero} σ _ = lift tt
  Frm⇒ {suc n} {Γ = Γₙ , Γₛₙ} {Δₙ , Δₛₙ} (σₙ , σₛₙ) =
    WebFrm⇒ Γₛₙ Δₛₙ σₙ σₛₙ

  Cns⇒ {zero} _ _ = lift tt
  Cns⇒ {suc n} {Γ = Γₙ , Γₛₙ} {Δₙ , Δₛₙ} (σₙ , σₛₙ) =
    Web⇒ Γₛₙ Δₛₙ σₙ σₛₙ
  
  --
  --  Composition
  --

  infixr 30 _⊚_
  
  _⊚_ : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Ctx n ℓ₀} {Δ : 𝕆Ctx n ℓ₁} {Θ : 𝕆Ctx n ℓ₂}
    → (Δ ⇒ Θ) → (Γ ⇒ Δ) → (Γ ⇒ Θ)

  postulate

    ⊚-Frm : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Ctx n ℓ₀} {Δ : 𝕆Ctx n ℓ₁} {Θ : 𝕆Ctx n ℓ₂}
      → (σ : Δ ⇒ Θ) (τ : Γ ⇒ Δ) (o : 𝒪 n) (f : Frm Γ o)
      → Frm⇒ (σ ⊚ τ) f ↦ Frm⇒ σ (Frm⇒ τ f)
    {-# REWRITE ⊚-Frm #-}

    ⊚-assoc : ∀ {n ℓ₀ ℓ₁ ℓ₂ ℓ₃}
      → {Γ : 𝕆Ctx n ℓ₀} {Δ : 𝕆Ctx n ℓ₁} {Θ : 𝕆Ctx n ℓ₂} {W : 𝕆Ctx n ℓ₃}
      → (σ : Θ ⇒ W) (τ : Δ ⇒ Θ) (γ : Γ ⇒ Δ)
      → (σ ⊚ τ) ⊚ γ ↦ σ ⊚ τ ⊚ γ
    {-# REWRITE ⊚-assoc #-}

    -- And unit laws ...

  _⊚_ {zero} σ τ = lift tt
  _⊚_ {suc n} {Γ = Γₙ , Γₛₙ} {Δₙ , Δₛₙ} {Θₙ , Θₛₙ} (σₙ , σₛₙ) (τₙ , τₛₙ) =
    σₙ ⊚ τₙ , λ x → σₛₙ (τₛₙ x)

  --
  --  Action of substitutions on types
  --

  -- Oh, shoot.  We should allow different universe in the contexts
  -- here ....
  
  _[_]ty : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Ctx n ℓ₀} {Δ : 𝕆Ctx n ℓ₁}
    → (X : 𝕆Type Δ ℓ₂) (σ : Γ ⇒ Δ) 
    → 𝕆Type Γ ℓ₂

  [_⊙_] : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Ctx n ℓ₀} {Δ : 𝕆Ctx n ℓ₁}
    → {X : 𝕆Type Δ ℓ₂} (σ : Γ ⇒ Δ)
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
    → Frm↓ (X [ σ ]ty) f 
    → Frm↓ X (Frm⇒ σ f)

  -- Again, to fix this, isolate the dimension in a module
  {-# TERMINATING #-}
  [_⊙_]c : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Ctx n ℓ₀} {Δ : 𝕆Ctx n ℓ₁}
    → {X : 𝕆Type Δ ℓ₂} (σ : Γ ⇒ Δ)
    → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm Γ 𝑜} {c : Cns Γ f 𝑝} 
    → {f↓ : Frm↓ (X [ σ ]ty) f} (c↓ : Cns↓ (X [ σ ]ty) f↓ c)
    → Cns↓ X [ σ ⊙ f↓ ] (Cns⇒ σ c)

  postulate

    Shp-⊙ : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Ctx n ℓ₀} {Δ : 𝕆Ctx n ℓ₁}
      → {X : 𝕆Type Δ ℓ₂} (σ : Γ ⇒ Δ)
      → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm Γ 𝑜} {c : Cns Γ f 𝑝} 
      → {f↓ : Frm↓ (X [ σ ]ty) f}
      → (c↓ : Cns↓ (X [ σ ]ty) f↓ c) (p : Pos 𝑝)
      → [ σ ⊙ Shp↓ (X [ σ ]ty) c↓ p ] ↦ Shp↓ X [ σ ⊙ c↓ ]c p 
    {-# REWRITE Shp-⊙ #-}

    η-⊙ : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Ctx n ℓ₀} {Δ : 𝕆Ctx n ℓ₁}
      → {X : 𝕆Type Δ ℓ₂} (σ : Γ ⇒ Δ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
      → (f↓ : Frm↓ (X [ σ ]ty) f)
      → [ σ ⊙ η↓ (X [ σ ]ty) f↓ ]c ↦ η↓ X [ σ ⊙ f↓ ]
    {-# REWRITE η-⊙ #-}

    μ-⊙ : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Ctx n ℓ₀} {Δ : 𝕆Ctx n ℓ₁}
      → {X : 𝕆Type Δ ℓ₂} (σ : Γ ⇒ Δ)
      → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm Γ 𝑜} {c : Cns Γ f 𝑝} 
      → {f↓ : Frm↓ (X [ σ ]ty) f} (c↓ : Cns↓ (X [ σ ]ty) f↓ c)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {d : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑞 p)}
      → (d↓ :  (p : Pos 𝑝) → Cns↓ (X [ σ ]ty) (Shp↓ (X [ σ ]ty) c↓ p) (d p))
      → [ σ ⊙ μ↓ (X [ σ ]ty) c↓ d↓ ]c ↦ μ↓ X [ σ ⊙ c↓ ]c (λ p → [ σ ⊙ d↓ p ]c)
    {-# REWRITE μ-⊙ #-}

  _[_]ty {zero} X σ = lift tt
  _[_]ty {suc n} (Xₙ , Xₛₙ) (σₙ , σₛₙ) =
    Xₙ [ σₙ ]ty , λ {𝑜} {f} f↓ γ → Xₛₙ [ σₙ ⊙ f↓ ] (σₛₙ γ)

  [_⊙_] {zero} σ f↓ = lift tt
  [_⊙_] {suc n} (σₙ , σₛₙ) {f = f , x , c , y} (f↓ , x↓ , c↓ , y↓) =
    [ σₙ ⊙ f↓ ] , x↓ , [ σₙ ⊙ c↓ ]c , y↓

  [_⊙_]c {zero} σ c↓ = lift tt
  [_⊙_]c {suc n} σ {c = lf x} idp = idp
  [_⊙_]c {suc n} (σₙ , σₛₙ) {c = nd x c y d z ψ} (c↓ , y↓ , d↓ , z↓ , ψ↓ , idp) =
    [ σₙ ⊙ c↓ ]c , y↓ , (λ p → [ σₙ ⊙ d↓ p ]c) , z↓ , (λ p → [ (σₙ , σₛₙ) ⊙ (ψ↓ p) ]c) , idp


