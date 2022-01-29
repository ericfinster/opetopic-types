--
--  OpetopicExt.agda - Extension of the context
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Prelude
open import Opetopes
open import OpetopicCtx
open import OpetopicSub 
open import OpetopicType
open import OpetopicTerm

module OpetopicExt where

  Ext : ∀ {n ℓ₀ ℓ₁} (Γ : 𝕆Ctx n ℓ₀) (X : 𝕆Type Γ ℓ₁)
    → 𝕆Ctx n (ℓ-max ℓ₀ ℓ₁) 

  π-ext : ∀ {n ℓ₀ ℓ₁} (Γ : 𝕆Ctx n ℓ₀) (X : 𝕆Type Γ ℓ₁)
    → Ext Γ X ⇒ Γ

  tm-ext : ∀ {n ℓ₀ ℓ₁} (Γ : 𝕆Ctx n ℓ₀) (X : 𝕆Type Γ ℓ₁)
    → 𝕆Term (X [ π-ext Γ X ]ty)

  Ext {zero} Γ X = lift tt
  Ext {suc n} (Γₙ , Γₛₙ) (Xₙ , Xₛₙ) =
    Ext Γₙ Xₙ , λ f → Σ[ γ ∈ Γₛₙ (Frm⇒ (π-ext Γₙ Xₙ) f) ] Xₛₙ
      [ π-ext Γₙ Xₙ ⊙ Frm-Tm (tm-ext Γₙ Xₙ) f ] γ

  π-ext {zero} Γ X = lift tt
  π-ext {suc n} (Γₙ , Γₛₙ) (Xₙ , Xₛₙ) =
    π-ext Γₙ Xₙ , fst

  tm-ext {zero} Γ X = lift tt
  tm-ext {suc n} (Γₙ , Γₛₙ) (Xₙ , Xₛₙ) =
    tm-ext Γₙ Xₙ , snd
