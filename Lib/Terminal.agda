open import Cubical.Foundations.Everything

open import Core.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Core.OpetopicType
open import Core.OpetopicMap 
open import Lib.Structures

module Lib.Terminal where

  𝕋 : ∀ {ℓ} (n : ℕ) → 𝕆Type n ℓ
  𝕋 zero = tt*
  𝕋 (suc n) = 𝕋 n , λ _ → Lift Unit

  𝕋Ext : ∀ {n ℓ} (X : 𝕆Type n ℓ) → 𝕆Type∞ X
  Fill (𝕋Ext X) = λ _ → Lift Unit
  Hom (𝕋Ext X) = 𝕋Ext _

  is-fib-ext-𝕋Ext : ∀ {n ℓ} {X : 𝕆Type n ℓ} → is-fibrant-ext (𝕋Ext X)
  fill-fib is-fib-ext-𝕋Ext f s = (tt* , tt*) , λ (tt* , tt*) → refl
  hom-fib is-fib-ext-𝕋Ext = is-fib-ext-𝕋Ext

  is-0-trunc-𝕋Ext : ∀ {n ℓ} {X : 𝕆Type n ℓ} → is-n-trunc 0 (𝕋Ext X)
  is-n-trunc.hLevel is-0-trunc-𝕋Ext f = tt* , λ _ → refl
  is-n-trunc.is-trunc-ext is-0-trunc-𝕋Ext = is-0-trunc-𝕋Ext

  ⇒𝕋 : ∀ {n ℓ} → (X : 𝕆Type n ℓ) → X ⇒ 𝕋 {ℓ-zero} n
  ⇒𝕋 {zero} X = tt*
  ⇒𝕋 {suc n} (X , P) = ⇒𝕋 X , λ _ → tt*
