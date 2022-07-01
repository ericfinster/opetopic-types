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

module Experimental.NoDecs.Sigma where

𝕋↓ : ∀ {n ℓ₀} (X : 𝕆Type n ℓ₀) (ℓ : Level) → 𝕆Fam X ℓ
𝕋↓ {zero} {ℓ₀} X ℓ = tt*
𝕋↓ {suc n} {ℓ₀} (X , P) ℓ = (𝕋↓ X ℓ) , (λ f x → Lift Unit)

𝕆Σ : ∀ {n ℓ} (X : 𝕆Type n ℓ) (X↓ : 𝕆Fam X ℓ) → 𝕆Type n ℓ

Fst : ∀ {n ℓ} {X : 𝕆Type n ℓ} {X↓ : 𝕆Fam X ℓ} → 𝕆Σ X X↓ ⇒ X
Snd : ∀ {n ℓ} {X : 𝕆Type n ℓ} {X↓ : 𝕆Fam X ℓ} → 𝕆Σ X X↓ ⇛[ Fst ] X↓

-- Not sure why there are positivity issues for Σ-cell here and not for prod-cell in CartesianProduct.agda
record Σ-cell {n ℓ} {X : 𝕆Type n ℓ} {X↓ : 𝕆Fam X ℓ}
  (P : Frm X → Type ℓ)
  (P↓ : {f : Frm X} (f↓ : Frm↓ X↓ f) → P f → Type ℓ)
  (f : Frm (𝕆Σ X X↓)) : Type ℓ where
  constructor _∣_
  field
    fstₒ : P (Frm⇒ Fst f)
    sndₒ : P↓ (Frm⇛ Snd f ) fstₒ
open Σ-cell

𝕆Σ {zero} X X↓ = tt*
𝕆Σ {suc n} (X , P) (X↓ , P↓) = 𝕆Σ X X↓ , Σ-cell P P↓

Fst {zero} = tt*
Fst {suc n} = Fst , fstₒ

Snd {zero} = tt*
Snd {suc n} = Snd , sndₒ
