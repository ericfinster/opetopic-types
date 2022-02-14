--
--  OpetopicMap.agda - Maps of opetopic types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat

open import Core.Prelude
open import Core.Opetopes
open import Core.OpetopicType
open import Core.OpetopicFamily

module Core.OpetopicMap where

  infixr 40 _⇒_

  _⇒_ : ∀ {n ℓ₀ ℓ₁} → 𝕆Type n ℓ₀ → 𝕆Type n ℓ₁
    → Type (ℓ-max ℓ₀ ℓ₁)

  Frm⇒ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁} (σ : X ⇒ Y)
    → {o : 𝒪 n} → Frm X o → Frm Y o
    
  Cns⇒ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁} (σ : X ⇒ Y)
    → {o : 𝒪 n} {𝑝 : 𝒫 o} {f : Frm X o}
    → Cns X f 𝑝 → Cns Y (Frm⇒ σ f) 𝑝

  postulate

    Shp-Frm⇒ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁} (σ : X ⇒ Y)
      → {o : 𝒪 n} {𝑝 : 𝒫 o} {f : Frm X o} (c : Cns X f 𝑝) (p : Pos 𝑝)
      → Frm⇒ σ (Shp X c p) ↦ Shp Y (Cns⇒ σ c) p
    {-# REWRITE Shp-Frm⇒ #-} 

    η⇒ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁} (σ : X ⇒ Y)
      → {o : 𝒪 n} (f : Frm X o)
      → Cns⇒ σ (η X f) ↦ η Y (Frm⇒ σ f)
    {-# REWRITE η⇒ #-} 

    μ⇒ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁} (σ : X ⇒ Y)
      → {o : 𝒪 n} {f : Frm X o}
      → {𝑝 : 𝒫 o} (c : Cns X f 𝑝)
      → {ι : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → (κ : (p : Pos 𝑝) → Cns X (Shp X c p) (ι p))
      → Cns⇒ σ (μ X c κ) ↦ μ Y (Cns⇒ σ c) (λ p → Cns⇒ σ (κ p))
    {-# REWRITE μ⇒ #-}

  _⇒_ {zero} _ _ = Lift Unit
  _⇒_ {suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) =
    Σ (Xₙ ⇒ Yₙ) (λ σ →
     {o : 𝒪 n} {f : Frm Xₙ o}
     → Xₛₙ f → Yₛₙ (Frm⇒ σ f))

  Frm⇒ σ {●} f = tt*
  Frm⇒ (σₙ , σₛₙ) {𝑜 ∣ 𝑝} (f , x , c , y) =
    Frm⇒ σₙ f , σₛₙ x , Cns⇒ σₙ c , λ p → σₛₙ (y p) 

  Cns⇒ σ {●} c = tt*
  Cns⇒ (σₙ , σₛₙ) {𝑜 ∣ ._} {𝑝 = lfₒ} (lf x) = lf (σₛₙ x)
  Cns⇒ (σₙ , σₛₙ) {𝑜 ∣ ._} {𝑝 = ndₒ 𝑝 𝑞 𝑟} (nd x c y d z ψ) = 
    nd (σₛₙ x) (Cns⇒ σₙ c) (σₛₙ ∘ y) (Cns⇒ σₙ ∘ d)
       (λ p q → σₛₙ (z p q)) (λ p → Cns⇒ (σₙ , σₛₙ) (ψ p))
       
  --
  --  The identity substitution
  --

  id-sub : ∀ {n ℓ} (X : 𝕆Type n ℓ) → X ⇒ X

  postulate

    id-frm : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → {𝑜 : 𝒪 n} (f : Frm X 𝑜)
      → Frm⇒ (id-sub X) f ↦ f
    {-# REWRITE id-frm #-}

    id-cns : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜}
      → (f : Frm X 𝑜) (c : Cns X f 𝑝)
      → Cns⇒ (id-sub X) c ↦ c
    {-# REWRITE id-cns #-}

  id-sub {zero} X = tt*
  id-sub {suc n} (Xₙ , Xₛₙ) = id-sub Xₙ , λ x → x
  
  --
  --  Composition
  --

  infixr 30 _⊚_
  
  _⊚_ : ∀ {n ℓ₀ ℓ₁ ℓ₂} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁} {Z : 𝕆Type n ℓ₂}
    → (Y ⇒ Z) → (X ⇒ Y) → (X ⇒ Z)

  postulate

    ⊚-Frm : ∀ {n ℓ₀ ℓ₁ ℓ₂} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁} {Z : 𝕆Type n ℓ₂}
      → (σ : Y ⇒ Z) (τ : X ⇒ Y) (o : 𝒪 n) (f : Frm X o)
      → Frm⇒ (σ ⊚ τ) f ↦ Frm⇒ σ (Frm⇒ τ f)
    {-# REWRITE ⊚-Frm #-}

    ⊚-assoc : ∀ {n ℓ₀ ℓ₁ ℓ₂ ℓ₃}
      → {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁} {Z : 𝕆Type n ℓ₂} {W : 𝕆Type n ℓ₃}
      → (σ : Z ⇒ W) (τ : Y ⇒ Z) (γ : X ⇒ Y)
      → (σ ⊚ τ) ⊚ γ ↦ σ ⊚ τ ⊚ γ
    {-# REWRITE ⊚-assoc #-}

    -- And unit laws ...

  _⊚_ {zero} σ τ = lift tt
  _⊚_ {suc n} {X = Xₙ , Xₛₙ} {Yₙ , Yₛₙ} {Zₙ , Zₛₙ} (σₙ , σₛₙ) (τₙ , τₛₙ) =
    σₙ ⊚ τₙ , λ x → σₛₙ (τₛₙ x)

  --
  --  Action of substitutions on familiesx
  --

  _[_]ty : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Type n ℓ₀} {Δ : 𝕆Type n ℓ₁}
    → (X : 𝕆Fam Δ ℓ₂) (σ : Γ ⇒ Δ) 
    → 𝕆Fam Γ ℓ₂

  [_⊙_] : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Type n ℓ₀} {Δ : 𝕆Type n ℓ₁}
    → {X : 𝕆Fam Δ ℓ₂} (σ : Γ ⇒ Δ)
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
    → Frm↓ (X [ σ ]ty) f 
    → Frm↓ X (Frm⇒ σ f)

  [_⊙_]c : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Type n ℓ₀} {Δ : 𝕆Type n ℓ₁}
    → {X : 𝕆Fam Δ ℓ₂} (σ : Γ ⇒ Δ)
    → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm Γ 𝑜} {c : Cns Γ f 𝑝} 
    → {f↓ : Frm↓ (X [ σ ]ty) f} (c↓ : Cns↓ (X [ σ ]ty) f↓ c)
    → Cns↓ X [ σ ⊙ f↓ ] (Cns⇒ σ c)

  postulate

    Shp-⊙ : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Type n ℓ₀} {Δ : 𝕆Type n ℓ₁}
      → {X : 𝕆Fam Δ ℓ₂} (σ : Γ ⇒ Δ)
      → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm Γ 𝑜} {c : Cns Γ f 𝑝} 
      → {f↓ : Frm↓ (X [ σ ]ty) f}
      → (c↓ : Cns↓ (X [ σ ]ty) f↓ c) (p : Pos 𝑝)
      → [ σ ⊙ Shp↓ (X [ σ ]ty) c↓ p ] ↦ Shp↓ X [ σ ⊙ c↓ ]c p 
    {-# REWRITE Shp-⊙ #-}

    η-⊙ : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Type n ℓ₀} {Δ : 𝕆Type n ℓ₁}
      → {X : 𝕆Fam Δ ℓ₂} (σ : Γ ⇒ Δ)
      → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
      → (f↓ : Frm↓ (X [ σ ]ty) f)
      → [ σ ⊙ η↓ (X [ σ ]ty) f↓ ]c ↦ η↓ X [ σ ⊙ f↓ ]
    {-# REWRITE η-⊙ #-}

    μ-⊙ : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Type n ℓ₀} {Δ : 𝕆Type n ℓ₁}
      → {X : 𝕆Fam Δ ℓ₂} (σ : Γ ⇒ Δ)
      → {𝑜 : 𝒪 n} {𝑝 : 𝒫 𝑜} {f : Frm Γ 𝑜} {c : Cns Γ f 𝑝} 
      → {f↓ : Frm↓ (X [ σ ]ty) f} (c↓ : Cns↓ (X [ σ ]ty) f↓ c)
      → {𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p)}
      → {d : (p : Pos 𝑝) → Cns Γ (Shp Γ c p) (𝑞 p)}
      → (d↓ :  (p : Pos 𝑝) → Cns↓ (X [ σ ]ty) (Shp↓ (X [ σ ]ty) c↓ p) (d p))
      → [ σ ⊙ μ↓ (X [ σ ]ty) c↓ d↓ ]c ↦ μ↓ X [ σ ⊙ c↓ ]c (λ p → [ σ ⊙ d↓ p ]c)
    {-# REWRITE μ-⊙ #-}

  _[_]ty {zero} X σ = tt*
  _[_]ty {suc n} (Xₙ , Xₛₙ) (σₙ , σₛₙ) =
    Xₙ [ σₙ ]ty , λ {𝑜} {f} f↓ γ → Xₛₙ [ σₙ ⊙ f↓ ] (σₛₙ γ)

  [_⊙_] σ {●} f↓ = tt*
  [_⊙_] (σₙ , σₛₙ) {𝑜 ∣ 𝑝} {f = f , x , c , y} (f↓ , x↓ , c↓ , y↓) =
    [ σₙ ⊙ f↓ ] , x↓ , [ σₙ ⊙ c↓ ]c , y↓

  [_⊙_]c σ {●} c↓ = tt*
  [_⊙_]c (σₙ , σₛₙ) {𝑜 ∣ ._} {𝑝 = lfₒ} {c = lf x} (lf↓ x↓) = lf↓ x↓ 
  [_⊙_]c (σₙ , σₛₙ) {𝑜 ∣ ._} {𝑝 = ndₒ 𝑝 𝑞 𝑟} {c = nd x c y d z ψ} (nd↓ x↓ c↓ y↓ d↓ z↓ ψ↓) =
    nd↓ x↓ [ σₙ ⊙ c↓ ]c y↓ (λ p → [ σₙ ⊙ d↓ p ]c) z↓ (λ p → [ (σₙ , σₛₙ) ⊙ (ψ↓ p) ]c) 

  --
  --  Infinite Dimensional Maps
  --

  record [_⇒_↓_] {n ℓ} {X Y : 𝕆Type n ℓ} (X∞ : 𝕆Type∞ X) (Y∞ : 𝕆Type∞ Y)
      (α : X ⇒ Y)  : Type ℓ where
    coinductive
    field
      Fill⇒ : {o : 𝒪 n} {f : Frm X o} → Fill X∞ f → Fill Y∞ (Frm⇒ α f)
      Hom⇒ : [ Hom X∞ ⇒ Hom Y∞ ↓ α , Fill⇒ ]

  --  Pulling back an extension along a substitution
  Pb∞ : ∀ {n ℓ} {X : 𝕆Type n ℓ} {Y : 𝕆Type n ℓ}
    → (σ : X ⇒ Y) → 𝕆Type∞ Y → 𝕆Type∞ X 
  Fill (Pb∞ {X = X} {Y} σ Y∞) {𝑜} f = Fill Y∞ (Frm⇒ σ f)
  Hom (Pb∞ {X = X} {Y} σ Y∞) =
    Pb∞ {X = (X , λ {𝑜} f → Fill Y∞ (Frm⇒ σ f))}
          {Y = (Y , Fill Y∞)} (σ , λ x → x) (Hom Y∞)
  
  --  Pushing forward and extension along a substitution
  Pf∞ : ∀ {n ℓ} {X : 𝕆Type n ℓ} {Y : 𝕆Type n ℓ}
    → (σ : X ⇒ Y) → 𝕆Type∞ X → 𝕆Type∞ Y
  Fill (Pf∞ {X = X} {Y} σ X∞) {o} f =
    Σ[ f' ∈ fiber (Frm⇒ σ) f ] Fill X∞ (fst f')
  Hom (Pf∞ {X = X} {Y} σ X∞) = Pf∞ {X = (X , Fill X∞)} {Y = (Y ,
       (λ {o} f → Σ-syntax (fiber (Frm⇒ σ) f) (λ f' → Fill X∞ (fst f'))))}
       (σ , λ {𝑜} {f} x → (f , refl) , x) (Hom X∞)
