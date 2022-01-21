{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import Opetopes
open import OpetopicType
open import OpetopicMap

module TheUniverse where

  𝕆U : ∀ {ℓ} (n : ℕ) → 𝕆 (ℓ-suc ℓ) n
  𝕆U* : ∀ {ℓ} (n : ℕ) → 𝕆 (ℓ-suc ℓ) n
  𝕦 : ∀ {ℓ} (n : ℕ) → 𝕆U* {ℓ} n ⇒ 𝕆U {ℓ} n

  𝕆U O = tt
  𝕆U {ℓ = ℓ} (S n) = 𝕆U n , λ {o} f →
    (f' : Frm (𝕆U* n) o) (e : Frm⇒ (𝕦 n) f' ≡ f)
    → Set ℓ
  
  𝕆U* O = tt
  𝕆U* {ℓ} (S n) = 𝕆U* n , λ {o} f* →
    Σ ((f' : Frm (𝕆U* n) o) (e : Frm⇒ (𝕦 n) f' ≡ Frm⇒ (𝕦 n) f*) → Set ℓ) (λ F → F f* refl)
  
  𝕦 O = tt
  𝕦 (S n) = 𝕦 n , λ {o} {f} X → fst X

  --
  -- Oh!  And Σ.  What about him?
  --

  -- Σₒ : ∀ {ℓ n} (X : 𝕆 ℓ n) (Y : X ⇒ 𝕆U {ℓ} n) → 𝕆 ℓ n
  -- fstₒ : ∀ {ℓ n} (X : 𝕆 ℓ n) (Y : X ⇒ 𝕆U {ℓ} n) → Σₒ X Y ⇒ X
  -- sndₒ : ∀ {ℓ n} (X : 𝕆 ℓ n) (Y : X ⇒ 𝕆U {ℓ} n) → Σₒ X Y ⇒ 𝕆U* {ℓ} n
  
  -- Σₒ {n = O} X Y = tt
  -- Σₒ {n = S n} (Xₙ , Xₛₙ) (Yₙ , Yₛₙ) =
  --   Σₒ Xₙ Yₙ , λ {o} f → Σ (Xₛₙ (Frm⇒ (fstₒ Xₙ Yₙ) f)) (λ x → {!!})
  
  -- fstₒ = {!!}

  -- sndₒ = {!!} 

  --
  --  A first test: suppose I have an opetopic type.  Does this
  --  determine a point of the universe?
  --

  classify : ∀ {ℓ} (n : ℕ) → 𝕆 ℓ n → 𝕋 {ℓ} n ⇒ 𝕆U {ℓ} n

  unclassify : ∀ {ℓ} (n : ℕ) (X : 𝕆 ℓ n) {o : 𝒪 n} 
    → (t : Frm (𝕋 n) o) (f : Frm (𝕆U* n) o)
    → (e : Frm⇒ (𝕦 n) f ≡ Frm⇒ (classify n X) t)
    → Frm X o 

  classify O _ = tt
  classify (S n) (Xₙ , Xₛₙ) = classify n Xₙ ,
    λ {o} {f} _ f' e → Xₛₙ (unclassify n Xₙ f f' e)
  
  unclassify O X t f e = tt
  unclassify (S n) (Xₙ , Xₛₙ) t f e = {!!}

  -- Yeah, so you need to see that pullbacks can be computed pointwise
  -- in trees.  But I think characterizing the identity types of frames
  -- and trees and so on will be done for a fixed n.  So I don't see
  -- that this will necessarily have any coherence problems.

