--
--  OpetopicSigma - Sigma of Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Prelude
open import Opetopes
open import OpetopicCtx
open import OpetopicType
open import OpetopicTerm
open import OpetopicSub 
open import OpetopicExt

module OpetopicSigma where

  Σₒ : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Ctx n ℓ₀}
    → (X : 𝕆Type Γ ℓ₁) (Y : 𝕆Type (Ext Γ X) ℓ₂)
    → 𝕆Type Γ (ℓ-max ℓ₀ ℓ₁)

  Frm-fst : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Ctx n ℓ₀}
    → (X : 𝕆Type Γ ℓ₁) (Y : 𝕆Type (Ext Γ X) ℓ₂)
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
    → Frm↓ (Σₒ X Y) f → Frm↓ X f

  Frm-snd : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Ctx n ℓ₀}
    → (X : 𝕆Type Γ ℓ₁) (Y : 𝕆Type (Ext Γ X) ℓ₂)
    → {𝑜 : 𝒪 n} {f : Frm Γ 𝑜}
    → (f↓ : Frm↓ (Σₒ X Y) f)
    → Frm↓ Y {!Frm-fst X Y f↓!} 

  Σₒ {zero} X Y = lift tt
  Σₒ {suc n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) =
    Σₒ Xₙ Yₙ , λ {f} f↓ γ → Σ[ x ∈ Xₛₙ (Frm-fst Xₙ Yₙ f↓) γ ] {!!}

  Frm-fst X Y f↓ = {!!} 
  Frm-snd X Y f↓ = {!!} 

  -- Hmmm. Name clash with opetopes ...
  Σₒ-pair : ∀ {n ℓ₀ ℓ₁ ℓ₂} {Γ : 𝕆Ctx n ℓ₀}
    → {X : 𝕆Type Γ ℓ₁} {Y : 𝕆Type (Ext Γ X) ℓ₂}
    → (x : 𝕆Term X) (y : 𝕆Term (Y [ ext-sub x ]ty))
    → 𝕆Term (Σₒ X Y) 
  Σₒ-pair = {!!} 
