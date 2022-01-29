--
--  OpetopicExt.agda - Extension of the context
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Prelude
open import Opetopes
open import OpetopicCtx
open import OpetopicType

module OpetopicExt where

  Ext : ∀ {n ℓ₀ ℓ₁} (Γ : 𝕆Ctx n ℓ₀) (X : 𝕆Type Γ ℓ₁) → 𝕆Ctx n (ℓ-max ℓ₀ ℓ₁) 


  Ext = {!!} 
