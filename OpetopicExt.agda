--
--  OpetopicExt.agda - Extension of the context
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Prelude
open import Opetopes
open import OpetopicType
open import OpetopicSub 
open import OpetopicFam
open import OpetopicTerm

module OpetopicExt where

  -- The definition is awkward, not least because it doesn't provide
  -- a pairing operation for frames.  I have not yet found a better
  -- alternative other than simply axiomatizing the intro an elims...
  -- So maybe redo this ...
  
  Ext : ∀ {n ℓ₀ ℓ₁} (Γ : 𝕆Type n ℓ₀) (X : 𝕆Fam Γ ℓ₁)
    → 𝕆Type n (ℓ-max ℓ₀ ℓ₁) 

  π-ext : ∀ {n ℓ₀ ℓ₁} (Γ : 𝕆Type n ℓ₀) (X : 𝕆Fam Γ ℓ₁)
    → Ext Γ X ⇒ Γ

  tm-ext : ∀ {n ℓ₀ ℓ₁} (Γ : 𝕆Type n ℓ₀) (X : 𝕆Fam Γ ℓ₁)
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

  -- Yeah, ummm, we should do this for arbitrary susbtitutions
  -- and then have the identity.  I think that is probably better.
  ext-sub : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Type n ℓ₀} {X : 𝕆Fam Γ ℓ₁}
    → 𝕆Term X → Γ ⇒ Ext Γ X

  postulate

    -- Are these really the natural equations?
    Frm-ext-sub : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Type n ℓ₀} {X : 𝕆Fam Γ ℓ₁}
      → (x : 𝕆Term X) {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
      → Frm⇒ (π-ext Γ X) (Frm⇒ (ext-sub x) f) ↦ f
    {-# REWRITE Frm-ext-sub #-}

    Tm-ext-sub : ∀ {n ℓ₀ ℓ₁} {Γ : 𝕆Type n ℓ₀} {X : 𝕆Fam Γ ℓ₁}
      → (x : 𝕆Term X) {𝑜 : 𝒪 n} (f : Frm Γ 𝑜)
      → [ π-ext Γ X ⊙ Frm-Tm (tm-ext Γ X) (Frm⇒ (ext-sub x) f) ] ↦ Frm-Tm x f
    {-# REWRITE Tm-ext-sub #-}
    
  ext-sub {zero} x = lift tt
  ext-sub {suc n} (xₙ , xₛₙ) = ext-sub {n} xₙ , λ γ → γ , xₛₙ γ

  
