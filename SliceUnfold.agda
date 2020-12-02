{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb

module SliceUnfold (M : 𝕄) (M↓ : 𝕄↓ M) where

  -- module Slices (M : 𝕄) (M↓ : 𝕄↓ M) where

  --
  --  First slice
  --

  Plbk₁ : 𝕄
  Plbk₁ = Pb M (Idx↓ M↓)

  Plbk↓₁ : 𝕄↓ Plbk₁
  Plbk↓₁ = Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)

  Slc₁ : 𝕄
  Slc₁ = Slice Plbk₁

  Slc↓₁ : 𝕄↓ Slc₁
  Slc↓₁ = Slice↓ Plbk↓₁

  Rel₁ : Set₁
  Rel₁ = Idx Slc₁ → Set

  CanonRel₁ : Rel₁
  CanonRel₁ = Idx↓ Slc↓₁

  --
  --  Second slice
  --

  Plbk₂ : 𝕄
  Plbk₂ = Pb Slc₁ (Idx↓ Slc↓₁)

  Plbk↓₂ : 𝕄↓ Plbk₂
  Plbk↓₂ = Pb↓ Slc↓₁ (Idx↓ Slc↓₁) (λ i j k → j == k)

  Slc₂ : 𝕄
  Slc₂ = Slice Plbk₂

  Slc↓₂ : 𝕄↓ Slc₂
  Slc↓₂ = Slice↓ Plbk↓₂

  Rel₂ : Set₁
  Rel₂ = Idx Slc₂ → Set 

  CanonRel₂ : Rel₂
  CanonRel₂ = Idx↓ Slc↓₂

  --
  --  Third slice
  --

  Plbk₃ : 𝕄
  Plbk₃ = Pb Slc₂ (Idx↓ Slc↓₂)

  Plbk↓₃ : 𝕄↓ Plbk₃
  Plbk↓₃ = Pb↓ Slc↓₂ (Idx↓ Slc↓₂) (λ i j k → j == k)

  Slc₃ : 𝕄
  Slc₃ = Slice Plbk₃

  Slc↓₃ : 𝕄↓ Slc₃
  Slc↓₃ = Slice↓ Plbk↓₃

  Rel₃ : Set₁
  Rel₃ = Idx Slc₃ → Set 

  CanonRel₃ : Rel₃
  CanonRel₃ = Idx↓ Slc↓₃



