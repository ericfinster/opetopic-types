{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import Opetopes
open import OpetopicType
open import OpetopicMap

module Join where

  -- The join of opetopic types.

  infixl 50 _★_ 

  _★_ : ∀ {ℓ n} (X Y : 𝕆 ℓ n) → 𝕆 ℓ n 

  jn-inl : ∀ {ℓ n} (X Y : 𝕆 ℓ n) → X ⇒ X ★ Y
  jn-inr : ∀ {ℓ n} (X Y : 𝕆 ℓ n) → Y ⇒ X ★ Y

  -- Hmmm.  But in this version, we don't have n fixed.  Oh, so you
  -- have to change the indexing and give separate definitions in
  -- lower dimensions.  Okay.  So three *different* data type
  -- defintiions.
  
  data JoinCell {ℓ n} (X Y : 𝕆 ℓ n) : {o : 𝒪 n} (f : Frm (X ★ Y) o) → Set ℓ where


  _★_ {n = O} X Y = tt
  _★_ {n = S O} (_ , X₀) (_ , Y₀) = tt , (λ u → X₀ u ⊔ Y₀ u)
  _★_ {n = S (S O)} ((_ , X₀) , X₁) ((_ , Y₀) , Y₁) = (tt , (λ u → X₀ u ⊔ Y₀ u)) , {!!}
  _★_ {n = S (S (S n))} X Y = {!!}

  jn-inl = {!!} 
  jn-inr = {!!} 
