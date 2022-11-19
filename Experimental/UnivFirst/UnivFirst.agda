--
--  UnivFirst.agda - attempt at a unverse-centric definition
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude

module Experimental.UnivFirst.UnivFirst where

  --
  --  Opetopic Types
  --

  𝕌Frm : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)
  𝕌Src : ∀ {n ℓ} → 𝕌Frm n ℓ → Type (ℓ-suc ℓ)

  𝕌FrmEl : ∀ {n ℓ} → 𝕌Frm n ℓ → Type ℓ 
  𝕌SrcEl : ∀ {n ℓ} (F : 𝕌Frm n ℓ) (S : 𝕌Src F)
    → 𝕌FrmEl F → Type ℓ 

  𝕌Frm zero ℓ = Unit*
  𝕌Frm (suc n) ℓ =
    Σ[ F ∈ 𝕌Frm n ℓ ]
    Σ[ S ∈ 𝕌Src F ]  -- Do we need more data here?
    ((f : 𝕌FrmEl F) → Type ℓ) 

  𝕌Src = {!!} 
  
  𝕌FrmEl {zero} F = Unit*
  𝕌FrmEl {suc n} (F , S , T) =
    Σ[ f ∈ 𝕌FrmEl F ]
    Σ[ s ∈ 𝕌SrcEl F S f ]
    T f 

  𝕌SrcEl = {!!} 


  -- So, like, the question now is if the notion of opetopic type
  -- itself is definable in these terms.  What should it be?
  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)
  𝕆Type zero ℓ = {!!}
  𝕆Type (suc n) ℓ = {!!}

