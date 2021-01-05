{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import Finitary

module NoneOneMany where


  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓) (M-fin : is-finitary M) where

    open import SliceAlg M M↓ 
    open import SliceUnfold M 
    open ExtUnfold M↓
    
    module _ (X₂ : Rel₂ ↓Rel₁) (is-fib-X₂ : is-fib₂ X₂)
             (X₃ : Rel₃ X₂) (is-fib X₃ : is-fib₃ X₃) where

      postulate

        η-nh : (i : Idx M) (j : Idx↓ M↓ i)
          → (ϕ : (p : Pos ExtSlc₁ (lf (i , j))) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ (lf (i , j)) p))
          → X₂ ((((i , j) , η M i , cst j) , (j , idp) , η↓ M↓ j , cst idp) , lf (i , j) , ϕ) 

        -- So.  This is the goal.  As we have seen, this will induce
        -- and equivalence with the canonical relation and allow us
        -- to iterate.
        goal : (i : Idx ExtSlc₁) (σ : Cns ExtSlc₁ i)
          → (ϕ : (p : Pos ExtSlc₁ σ) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ σ p))
          → X₂ ((i , slc-idx i σ ϕ) , σ , ϕ) 

        -- What we will also need is that, under the above induced
        -- equivalence, the "unit" *use* X₃'s lf hypothesis.

      goal-test : (i : Idx ExtSlc₁) (σ : Cns ExtSlc₁ i)
        → (ϕ : (p : Pos ExtSlc₁ σ) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ σ p))
        → X₂ ((i , slc-idx i σ ϕ) , σ , ϕ) 
      goal-test ((i , j) , ._ , ._) (lf .(i , j)) ϕ = η-nh i j ϕ
      goal-test ((i , j) , ._ , ._) (nd c δ ε) ϕ with is-fin-disc (Pos M (fst c)) (M-fin (fst c))
        (record { P = λ p → is-node (ε p) ;
                  P-is-prop = λ p → Trunc-level ;
                  P-is-dec = λ p → slice-is-dec (ε p) })
      goal-test ((i , j) , .(μ M (fst c) (fst ∘ δ)) , _) (nd c δ ε) ϕ | inl p = {!!} -- The multi-valued case
      goal-test ((i , j) , .(μ M (fst c) (fst ∘ δ)) , _) (nd c δ ε) ϕ | inr ¬p = {!!} -- The corolla case



        -- And here is where we need to split: either we are looking at
        -- a corolla, or else there is a non-trivial gluing.  In the
        -- former case, use the unit of X₃.  In the latter, use induction
        -- to get a decoration by elements of X₂ and compose them.

        -- So, what it seems to me we need is that it is decidable
        -- whether or not the provided decoration is trivial or not.
        -- This is what should let us match in this case.  I believe
        -- this will be the case for any slice of the identity, since
        -- the postions are finite and decidable.
