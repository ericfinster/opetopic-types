{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import OpetopicType
open import FundamentalThm

module SliceUnique (M : 𝕄) (M↓ : 𝕄↓ M) where

  open import SliceUnfold M
  open ExtUnfold M↓

  -- Yeah, it really seems that you should be able to eliminate away
  -- the bottom equivalence and just be working over the index fibration.
  -- So, in that case, what exactly is the difference between this
  -- and your setup before?

  -- Intersting, yeah, you start with R : Rel₂.  I see. So you start
  -- working assuming that the constructors are given.  And I think this
  -- is exactly the point: this is one step too far.  You need to know
  -- that the equivalence on constructors is given by application of the
  -- fundamental theorem, and *then* you should be able to show that 

  module _ (is-alg : is-algebraic M M↓) 
           (X₁ : Rel₁ (Idx↓ M↓)) (is-fib-X₁ : is-fib₁ X₁)
           (X₂ : Rel₂ X₁) (is-fib-X₂ : is-fib₂ X₂)
           (hyp : (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
                  → X₁ ((i , idx (contr-center (is-alg i c ν))) , (c , ν)))
           where
  
    -- So, this will be just a composition of the fundamental
    -- theorem.
    to-show : (i : Idx ExtSlc₁) → Idx↓ ExtSlc↓₁ i ≃ X₁ i
    to-show = {!!} 

    open import SliceAlg M M↓

    -- And then *this* amounts to saying that the above identification
    -- is a homomorphism, which I feel must be the case.
    and-this : (i : Idx ExtSlc₁) (σ : Cns ExtSlc₁ i)
      → (ν : (p : Pos ExtSlc₁ σ) → X₁ (Typ ExtSlc₁ σ p))
      → X₂ ((i , –> (to-show i) (slc-idx i σ (λ p → <– (to-show (Typ ExtSlc₁ σ p)) (ν p)))) , (σ , ν))
    and-this = {!!}
    

