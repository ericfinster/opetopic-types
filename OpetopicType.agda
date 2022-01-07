{-# OPTIONS --without-K --rewriting --no-positivity-check #-}

open import MiniHoTT
open import Opetopes

module OpetopicType where

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  Frm : ∀ {ℓ n} → 𝕆 ℓ n → 𝒪 n → Set ℓ 
  Pd : ∀ {ℓ n} (X : 𝕆 ℓ n) (o : 𝒪 n) (f : Frm X o) → Set ℓ 

  𝕆 ℓ O = Set ℓ
  𝕆 ℓ (S n) = {!!}
  
  Frm X = {!!} 
  Pd X f = {!!} 
