--
--  Opposite.agda - Opetopic types with 1-arrows reversed
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum
open import Cubical.Data.Bool

open import Core.Prelude
open import Experimental.NoDecs.OpetopicType
open import Experimental.NoDecs.Structures

module Experimental.NoDecs.Opposite where

Op : ∀ {n ℓ} → 𝕆Type n ℓ → 𝕆Type n ℓ

postulate
  Op-involution : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    → Op (Op X) ↦ X
  {-# REWRITE Op-involution #-}

Frm-Op : ∀ {n ℓ} {X : 𝕆Type n ℓ} → Frm X → Frm (Op X)
Src-Op : ∀ {n ℓ} {X : 𝕆Type n ℓ} (P : Frm X → Type ℓ) {f : Frm X} → Src P f → Src (λ fᵒᵖ → P (Frm-Op fᵒᵖ)) (Frm-Op f)

postulate
  Frm-Op-involution : ∀ {n ℓ} {X : 𝕆Type n ℓ} (f : Frm X)
    → Frm-Op (Frm-Op f) ↦ f
  {-# REWRITE Frm-Op-involution #-}

Op {zero} X = tt*
Op {suc n} (X , P) = Op X , λ fᵒᵖ → P (Frm-Op fᵒᵖ)

Frm-Op {zero} f = tt*
Frm-Op {suc zero} {X = X , P} (f , s , t) = tt* , t , s
Frm-Op {suc (suc n)} {X = X , P} (f , s , t) = Frm-Op f , Src-Op P s , t

{-
Src-Op {zero} {ℓ} {X} P {f} x = x
Src-Op {suc zero} {ℓ} {X} P {f , s , t} x = {!!}
Src-Op {suc (suc n)} {ℓ} {X} P {f} x = {!!}
-}
