{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import OpetopicType

module SliceUnfold (M : 𝕄) where
  
  --
  --  First slice
  --

  Rel₀ : Set₁
  Rel₀ = Idx M → Set

  module _ (X₀ : Rel₀) where
  
    Plbk₁ : 𝕄
    Plbk₁ = Pb M X₀

    Slc₁ : 𝕄
    Slc₁ = Slice Plbk₁

    Rel₁ : Set₁
    Rel₁ = Idx Slc₁ → Set

  --
  --  Second slice
  --

  module _ {X₀ : Rel₀} (X₁ : Rel₁ X₀) where

    is-fib₁ : Set
    is-fib₁ = unique-action M X₀ X₁ 

    Plbk₂ : 𝕄
    Plbk₂ = Pb (Slc₁ X₀) X₁

    Slc₂ : 𝕄
    Slc₂ = Slice Plbk₂

    Rel₂ : Set₁
    Rel₂ = Idx Slc₂ → Set 

  --
  --  Third slice
  --

  module _ {X₀ : Rel₀} {X₁ : Rel₁ X₀} (X₂ : Rel₂ X₁) where

    is-fib₂ : Set
    is-fib₂ = unique-action (Slc₁ X₀) X₁ X₂

    Plbk₃ : 𝕄
    Plbk₃ = Pb (Slc₂ X₁) X₂

    Slc₃ : 𝕄
    Slc₃ = Slice Plbk₃

    Rel₃ : Set₁
    Rel₃ = Idx Slc₃ → Set 

  is-fib₃ : {X₀ : Rel₀} {X₁ : Rel₁ X₀} {X₂ : Rel₂ X₁}
    → Rel₃ X₂ → Set
  is-fib₃ {X₀} {X₁} {X₂} X₃ =
    unique-action (Slc₂ X₁) X₂ X₃  

  --
  --  Specializations for the case of an extension
  --

  module ExtUnfold (M↓ : 𝕄↓ M) where

    ↓Rel₀ : Rel₀
    ↓Rel₀ = Idx↓ M↓ 

    -- First slice
    ExtPlbk₁ : 𝕄
    ExtPlbk₁ = Plbk₁ ↓Rel₀
    
    ExtPlbk↓₁ : 𝕄↓ ExtPlbk₁
    ExtPlbk↓₁ = Pb↓ M↓ ↓Rel₀ (λ i j k → j == k)

    ExtSlc₁ : 𝕄
    ExtSlc₁ = Slc₁ ↓Rel₀
    
    ExtSlc↓₁ : 𝕄↓ ExtSlc₁
    ExtSlc↓₁ = Slice↓ ExtPlbk↓₁ 

    ↓Rel₁ : Rel₁ ↓Rel₀
    ↓Rel₁ = Idx↓ ExtSlc↓₁ 

    -- Second slice
    ExtPlbk₂ : 𝕄
    ExtPlbk₂ = Plbk₂ ↓Rel₁
    
    ExtPlbk↓₂ : 𝕄↓ ExtPlbk₂
    ExtPlbk↓₂ = Pb↓ ExtSlc↓₁ ↓Rel₁ (λ i j k → j == k)

    ExtSlc₂ : 𝕄
    ExtSlc₂ = Slc₂ ↓Rel₁
    
    ExtSlc↓₂ : 𝕄↓ ExtSlc₂
    ExtSlc↓₂ = Slice↓ ExtPlbk↓₂ 
