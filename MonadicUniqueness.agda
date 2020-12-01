{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import OpetopicType
open import IdentityMonad
open import IdentityMonadOver
open import SliceUnfold

module MonadicUniqueness (A : Set) where

  open Slices IdMnd (IdMnd↓ A)

  module _ (R : Rel₂) (is-fib-R : unique-action Slc₁ (Idx↓ Slc↓₁) R) 
           (T : Rel₃) (is-fib-T : unique-action Slc₂ (Idx↓ Slc↓₂) T) where

    -- Okay, so is it now true that I can prove R is composition?
    
    R-lf-η↓ : (i : Idx IdMnd) (j : Idx↓ (IdMnd↓ A) i)
      → R ((((i , j) , _ , _) , (j , idp) , η↓ (IdMnd↓ A) {i = i}  j , cst idp) , lf (i , j) , ⊥-elim) 
    R-lf-η↓ ttᵢ a = {!!}

    R-fib-gives : (i : Idx Slc₁) (c : Cns Slc₁ i)
      → (ν : (p : Pos Slc₁ c) → (Idx↓ Slc↓₁) (Typ Slc₁ c p))
      → Σ (Idx↓ Slc↓₁ i) (λ i↓ → R ((i , i↓) , c , ν))
    R-fib-gives i c ν = contr-center (is-fib-R i c ν) 

    R-fib-gives' : (i : Idx Slc₁)
      → (ω : Cns Slc₁ i)
      → (θ : (p : Pos Slc₁ ω) → (Idx↓ Slc↓₁) (Typ Slc₁ ω p))
      → Σ (Idx↓ Slc↓₁ i) (λ i↓ → R ((i , i↓) , ω , θ))
    R-fib-gives' i ω θ = contr-center (is-fib-R i ω θ) 

    R-fib-gives'' : (i : Idxᵢ) (a₀ : A) (c : Cnsᵢ i) (ν : (p : Posᵢ {u = i} c) → A)
      → (ω : Cns Slc₁ ((i , a₀) , c , ν))
      → (θ : (p : Pos Slc₁ ω) → (Idx↓ Slc↓₁) (Typ Slc₁ ω p))
      → Σ (Idx↓ Slc↓₁ ((i , a₀) , c , ν)) (λ i↓ → R ((((i , a₀) , c , ν) , i↓) , ω , θ))
    R-fib-gives'' i a₀ c ν ω θ = contr-center (is-fib-R ((i , a₀) , c , ν) ω θ) 

    to : (i : Idx Slc₂) → CanonRel₂ i → R i
    to ((((i , a₀) , c , ν) , (a₁ , p) , c↓ , typ-c↓=ν) , ω , θ) ((._ , idp) , ω↓ , θ↓) = {!ν!}
    -- to ((((i , a₀) , ._ , ._) , (a₁ , p) , ._ , ._) , ._ , θ) ((._ , idp) , lf↓ (.a₁ , .p) , θ↓) = {!i!}
    -- to ((((i , a₀) , ._ , ._) , (a₁ , p) , ._ , ._) , ._ , θ) ((._ , idp) , nd↓ (c↓ , ν↓) δ↓ ε↓ , θ↓) = {!!}

    -- So, to prove that R is composition is to prove the following:
    thm : (i : Idx Slc₂) → R i ≃ CanonRel₂ i
    thm ((((i , a₀) , c , ν) , (a₁ , p) , c↓ , typ-c↓=ν) , ω , θ) = {!!} 
