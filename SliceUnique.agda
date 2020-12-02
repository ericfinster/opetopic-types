{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import OpetopicType
open import FundamentalThm

module SliceUnique (M : 𝕄) (M↓ : 𝕄↓ M) where

  open import SliceUnfold M M↓
  open import SliceAlg M M↓

  --  This is type hypothesis that I think we will need to
  --  show for a relation R.  So first I will show that this
  --  hypothesis implies that R is equivalent to the canonical
  --  relation.
  
  R-hypothesis : Rel₂ → Set
  R-hypothesis R =
        (i : Idx Slc₁) (σ : Cns Slc₁ i)
      → (ϕ : (p : Pos Slc₁ σ) → Idx↓ Slc↓₁ (Typ Slc₁ σ p))
      → R ((i , slc-idx i σ ϕ) , (σ , ϕ)) 

  --  In this module, I will assume R is fibrant and satisfies
  --  the hypothesis above.  Then I claim that theorem follows
  --  from the Fundamental Theorem of HoTT.
  
  module RIsCanonical (R : Rel₂) (is-fib-R : unique-action Slc₁ (Idx↓ Slc↓₁) R)
                      (R-hyp : R-hypothesis R) where

    -- First, since R is fibrant, we can describe it as an identity
    -- type.  And the hypothesis on R allows us to say *exactly which
    -- identity type* it is equivalent to.
    
    R-is-== : (i : Idx Slc₁) (σ : Cns Slc₁ i)
      → (ϕ : (p : Pos Slc₁ σ) → Idx↓ Slc↓₁ (Typ Slc₁ σ p))
      → (a : Idx↓ Slc↓₁ i)
      → R ((i , a) , (σ , ϕ)) ≃ (slc-idx i σ ϕ == a)
    R-is-== i σ ϕ a = fundamental-thm A P a₀ r (is-fib-R i σ ϕ) a

      where A : Set
            A = Idx↓ Slc↓₁ i 

            P : A → Set
            P a = R ((i , a) , σ , ϕ)

            a₀ : A
            a₀ = slc-idx i σ ϕ

            r : P a₀
            r = R-hyp i σ ϕ

    open import SliceAlgebraic

    --  Next, the proof that the slice of monad extension is 
    --  always algebraic is exactly the proof that the canonical
    --  relation is fibrant.

    canon-is-fib : unique-action Slc₁ (Idx↓ Slc↓₁) CanonRel₂
    canon-is-fib = alg-mnd-has-unique-action Slc₁ Slc↓₁ (slc-algebraic M M↓) 

    --  Since we show that the canonical relation is fibrant by
    --  explicitly constructing an element and showing that it 
    --  is unique, this lets us again use the fundamental theorem
    --  to describe the canonical relation of an identity type.
    
    Canon-is-== : (i : Idx Slc₁) (σ : Cns Slc₁ i)
      → (ϕ : (p : Pos Slc₁ σ) → Idx↓ Slc↓₁ (Typ Slc₁ σ p))
      → (a : Idx↓ Slc↓₁ i)
      → CanonRel₂ ((i , a) , (σ , ϕ)) ≃ (slc-idx i σ ϕ == a)
    Canon-is-== i σ ϕ a = fundamental-thm A P a₀ r (canon-is-fib i σ ϕ) a 

      where A : Set
            A = Idx↓ Slc↓₁ i 

            P : A → Set
            P a = CanonRel₂ ((i , a) , σ , ϕ)

            a₀ : A
            a₀ = slc-idx i σ ϕ

            r : P a₀
            r = (slc-idx i σ ϕ , idp) , slc-cns i σ ϕ , slc-typ i σ ϕ

    --  We chose the hypothesis on R exactly so that the two
    --  equality types given by the fundamental theorem come
    --  out to be the same.  So now we can just compose these
    --  two equivalences to obtain the theorem we want:

    R-is-CanonRel : (i : Idx Slc₂) → R i ≃ CanonRel₂ i
    R-is-CanonRel ((i , a) , σ , ϕ) = (Canon-is-== i σ ϕ a) ⁻¹ ∘e (R-is-== i σ ϕ a)  


