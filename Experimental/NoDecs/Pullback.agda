{-# OPTIONS --type-in-type #-}
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
open import Experimental.NoDecs.OpetopicType

module Experimental.NoDecs.Pullback where

  -- Pulling back is also definable!
  Pb : ∀ {n ℓ} {A B C : 𝕆Type n ℓ} (σ : A ⇒ C) (τ : B ⇒ C) → 𝕆Type n ℓ
  πA : ∀ {n ℓ} {A B C : 𝕆Type n ℓ} (σ : A ⇒ C) (τ : B ⇒ C) → Pb σ τ ⇒ A
  πB : ∀ {n ℓ} {A B C : 𝕆Type n ℓ} (σ : A ⇒ C) (τ : B ⇒ C) → Pb σ τ ⇒ B
  π≡ : ∀ {n ℓ} {A B C : 𝕆Type n ℓ} (σ : A ⇒ C) (τ : B ⇒ C) → σ ⊙ (πA σ τ) ≡ τ ⊙ (πB σ τ)

  Pb {zero} σ τ = tt*
  Pb {suc n} {A = A , A'} {B , B'} {C , C'} (σ , σ') (τ , τ') = Pb σ τ , λ f →
    Σ[ a ∈ A' (Frm⇒ (πA σ τ) f) ]
    Σ[ b ∈ B' (Frm⇒ (πB σ τ) f) ]
    PathP (λ i → C' (Frm⇒ (π≡ σ τ i) f)) (σ' a) (τ' b)

  πA {zero} σ τ = tt*
  πA {suc n} (σ , σ') (τ , τ') = πA σ τ , λ { (a , b , p) → a }
  
  πB {zero} σ τ = tt*
  πB {suc n} (σ , σ') (τ , τ') = πB σ τ , λ { (a , b , p) → b }
  
  π≡ {zero} σ τ = refl
  π≡ {suc n} (σ , σ') (τ , τ') i =
    π≡ σ τ i , λ { (a , b , p) → p i }

