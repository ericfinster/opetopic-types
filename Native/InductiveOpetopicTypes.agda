{-# OPTIONS --no-positivity-check #-}
--
--  OpetopicType.agda - Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude

module Native.InductiveOpetopicTypes where

  data 𝕆Type (ℓ : Level) : Type (ℓ-suc ℓ) 

  Frm : ∀ {ℓ} → 𝕆Type ℓ → Type ℓ
  Src : ∀ {ℓ} {X : 𝕆Type ℓ} (P : Frm X → Type ℓ) → Frm X → Type ℓ 
  Pos : ∀ {ℓ} {X : 𝕆Type ℓ} (P : Frm X → Type ℓ)
    → {f : Frm X} → Src P f → Type ℓ

  data 𝕆Type ℓ where
    ● : 𝕆Type ℓ
    _▸_ : (X : 𝕆Type ℓ) (P : Frm X → Type ℓ) → 𝕆Type ℓ 

  Frm ● = Unit*
  Frm (X ▸ P) =
    Σ[ frm ∈ Frm X ]
    Σ[ src ∈ Src {X = X} P frm ]
    P frm

  Src = {!!} 
  Pos = {!!} 
