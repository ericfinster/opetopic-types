{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Algebricity
open import Pb
open import Finitary
open import AlgEqvElim
open import NoneOneMany

module Many where

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓) (M-fin : is-finitary M) where

    open import SliceAlg M M↓ 
    open import SliceUnfold M 
    open ExtUnfold M↓

    module _ (X₂ : Rel₂ ↓Rel₁) (is-fib-X₂ : is-fib₂ X₂) (alg-fib : AlgFib M M↓ X₂ is-fib-X₂)
             (X₃ : Rel₃ X₂) (is-fib-X₃ : is-fib₃ X₃) where

      open AlgFib alg-fib

      open Fibs M M↓ is-alg M-fin X₂ is-fib-X₂ alg-fib X₃ is-fib-X₃

      alg-eqv : AlgEqv ExtSlc₁ ExtSlc↓₁ X₂ X₃ is-fib-X₃
      AlgEqv.e alg-eqv i = alg-eqv-to i , alg-eqv-is-equiv i
      AlgEqv.η-hyp alg-eqv (((i , j) , c , ν) , (j , idp) , (c↓ , ν↓)) (._ , idp) = {!!}
      AlgEqv.μ-hyp alg-eqv (._ , ._) (lf (i , j) , ϕ) κ (((.j , idp) , ._ , ._) , idp) (lf↓ .(j , idp) , ϕ↓) κ↓ = {!!}
      AlgEqv.μ-hyp alg-eqv (._ , ._) (nd {i = i , j} c δ ε , ϕ) κ (((.j , idp) , ._ , ._) , idp) (nd↓ c↓ δ↓ ε↓ , ϕ↓) κ↓ = {!!}
