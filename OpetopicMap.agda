{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import Opetopes
open import OpetopicType

module OpetopicMap where

  _⇒_ : ∀ {ℓ₀ ℓ₁ n} → 𝕆 ℓ₀ n → 𝕆 ℓ₁ n
    → Set (ℓ-max ℓ₀ ℓ₁)

  Frm⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} (α : X ⇒ Y)
    → {o : 𝒪 n} → Frm X o → Frm Y o
    
  Cns⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} (α : X ⇒ Y)
    → {o : 𝒪 n} {ρ : 𝒫 o} {f : Frm X o}
    → Cns X f ρ → Cns Y (Frm⇒ α f) ρ

  postulate

    Shp-Frm⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} (α : X ⇒ Y)
      → {o : 𝒪 n} {ρ : 𝒫 o} {f : Frm X o} (c : Cns X f ρ) (p : Pos ρ)
      → Frm⇒ α (Shp X c p) ↦ Shp Y (Cns⇒ α c) p
    {-# REWRITE Shp-Frm⇒ #-} 

    η⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} (α : X ⇒ Y)
      → {o : 𝒪 n} (f : Frm X o)
      → Cns⇒ α (η X f) ↦ η Y (Frm⇒ α f)
    {-# REWRITE η⇒ #-} 

    μ⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆 ℓ₀ n} {Y : 𝕆 ℓ₁ n} (α : X ⇒ Y)
      → {o : 𝒪 n} {f : Frm X o}
      → {ρ : 𝒫 o} (c : Cns X f ρ)
      → {ι : (p : Pos ρ) → 𝒫 (Typ ρ p)}
      → (κ : (p : Pos ρ) → Cns X (Shp X c p) (ι p))
      → Cns⇒ α (μ X c κ) ↦ μ Y (Cns⇒ α c) (λ p → Cns⇒ α (κ p))
    {-# REWRITE μ⇒ #-}

  module _ {ℓ₀ ℓ₁ n} {Xₙ : 𝕆 ℓ₀ n} {Yₙ : 𝕆 ℓ₁ n}
           (Xₛₙ : {o : 𝒪 n} → Frm Xₙ o → Set ℓ₀)
           (Yₛₙ : {o : 𝒪 n} → Frm Yₙ o → Set ℓ₁)
           (αₙ : Xₙ ⇒ Yₙ) (αₛₙ : {o : 𝒪 n} {f : Frm Xₙ o} → Xₛₙ f → Yₛₙ (Frm⇒ αₙ f)) where

    -- Bingo!
    WebFrm⇒ : {o : 𝒪 n} {ρ : 𝒫 o}
      → WebFrm Xₙ Xₛₙ o ρ → WebFrm Yₙ Yₛₙ o ρ 
    WebFrm⇒ φ = ⟪ Frm⇒ αₙ (frm φ) , Cns⇒ αₙ (cns φ) ,
                  αₛₙ (tgt φ) , (λ p → αₛₙ (src φ p)) ⟫ 

    Web⇒ : {o : 𝒪 n} {ρ : 𝒫 o}
      → {φ : WebFrm Xₙ Xₛₙ o ρ} {τ : 𝒯r o ρ}
      → Web Xₙ Xₛₙ φ τ → Web Yₙ Yₛₙ (WebFrm⇒ φ) τ 
    Web⇒ (lf x) = lf (αₛₙ x)
    Web⇒ (nd φ ι κ δ ν ε) =
      nd (WebFrm⇒ φ) ι κ
        (λ p → Cns⇒ αₙ (δ p))
        (λ p q → αₛₙ (ν p q))
        (λ p → Web⇒ (ε p))

  _⇒_ {n = O} _ _ = ⊤
  _⇒_ {n = S n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) =
    Σ (Xₙ ⇒ Yₙ) (λ α →
     {o : 𝒪 n} {f : Frm Xₙ o}
     → Xₛₙ f → Yₛₙ (Frm⇒ α f))

  Frm⇒ {n = O} α _ = tt
  Frm⇒ {n = S n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} (αₙ , αₛₙ) =
    WebFrm⇒ Xₛₙ Yₛₙ αₙ αₛₙ

  Cns⇒ {n = O} _ _ = tt
  Cns⇒ {n = S n} {Xₙ , Xₛₙ} {Yₙ , Yₛₙ} (αₙ , αₛₙ) =
    Web⇒ Xₛₙ Yₛₙ αₙ αₛₙ
  
