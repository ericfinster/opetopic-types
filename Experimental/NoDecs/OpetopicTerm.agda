{-# OPTIONS --no-positivity-check #-}
--
--  Sigma.agda - Dependent sum of opetopic families
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude
open import Experimental.NoDecs.OpetopicType
open import Experimental.NoDecs.OpetopicFamily

module Experimental.NoDecs.OpetopicTerm where

  𝕆Term : ∀ {n ℓ₀ ℓ₁} (X : 𝕆Type n ℓ₀) (X↓ : 𝕆Fam X ℓ₁)
    → Type (ℓ-max ℓ₀ ℓ₁)

  postulate
  
    TmFrm : ∀ {n ℓ₀ ℓ₁} (X : 𝕆Type n ℓ₀) (X↓ : 𝕆Fam X ℓ₁)
      → (τ : 𝕆Term X X↓)
      → (f : Frm X) → Frm↓ X↓ f

    SrcFrm : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} (P : Frm X → Type ℓ₀)
      → {X↓ : 𝕆Fam X ℓ₁} (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ₁)
      → (τ : 𝕆Term X X↓)
      → {f : Frm X} (s : Src P f)
      → Src↓ P↓ (TmFrm X X↓ τ f) s 

  𝕆Term {zero} X X↓ = Lift Unit
  𝕆Term {suc n} (X , P) (X↓ , P↓) =
    Σ[ τ ∈ 𝕆Term X X↓ ] ({f : Frm X} (p : P f) → P↓ (TmFrm X X↓ τ f) p) 

  
  

