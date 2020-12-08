{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import OpetopicType
open import FundamentalThm
open import MonadEqv 
open import SliceUnfold
open import SliceAlgebraic

module SliceUnique where

  -- Here, I believe is the proper coinductive statement
  -- of the theorem:

  alg↓-unique : (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓)
    → (X : OpetopicType M) (is-fib : is-fibrant X)
    → (ob≃ : (i : Idx M) → Idx↓ M↓ i ≃ Ob X i)
    → (witness : (i : Idx M) (c : Cns M i)
               → (ν : (p : Pos M c) → Ob X (Typ M c p))
               → Ob (Hom X) ((i , –> (ob≃ i) (idx (contr-center (is-alg i c (λ p → <– (ob≃ (Typ M c p)) (ν p)))))) , c , ν))
    → ↓-to-OpType M M↓ ≃ₒ X 
  Ob≃ (alg↓-unique M M↓ is-alg X is-fib ob≃ witness) = ob≃
  Hom≃ (alg↓-unique M M↓ is-alg X is-fib ob≃ witness) =
    let open ExtUnfold M M↓ in
    alg↓-unique ExtSlc₁ ExtSlc↓₁ (slc-algebraic M M↓)
      (op-transp (Slice≃ (Pb≃' ob≃)) (Hom X))
      (op-transp-fib (Slice≃ (Pb≃' ob≃)) (Hom X) (hom-fibrant is-fib))
      {!!}
      {!!}

  -- We are left with two proof obligations, which, after eliminating
  -- away the equivalence by univalence, become the following:

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓) 
           (X₁ : Rel₁ M (Idx↓ M↓)) (is-fib-X₁ : is-fib₁ M X₁)
           (X₂ : Rel₂ M X₁) (is-fib-X₂ : is-fib₂ M X₂)
           (witness : (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
                    → X₁ ((i , idx (contr-center (is-alg i c ν))) , (c , ν)))
           where

    open ExtUnfold M M↓
    open import SliceAlg M M↓

    -- The next equivalence is given generically by the
    -- fundamental theorem, which says both the spaces may
    -- be expressed as identity types.
    
    next-ob≃ : (i : Idx ExtSlc₁) → Idx↓ ExtSlc↓₁ i ≃ X₁ i
    next-ob≃ ((i , j) , c , ν) =
      
      Idx↓ ExtSlc↓₁ ((i , j) , c , ν)         ≃⟨ {!!} ⟩  -- by the fundamental theorem
      j == idx (contr-center (is-alg i c ν))  ≃⟨ {!!} ⟩  -- again, by the fundamental theorem, using "witness"
      X₁ ((i , j) , c , ν) ≃∎

    -- It may be useful, however, to prove the above equivalence
    -- directly so that we have better control over the image of
    -- various elements....

    -- In any case, we have now reduced ourselves to the following:
    -- we have to find a witness in X₂ showing that it coincides
    -- with the proof that the slice is algebraic.  This should be
    -- carried out via induction, now with the extra hypothesis that
    -- X₁ witnesses multiplication in the algebra.

    next-witness : (i : Idx ExtSlc₁) (σ : Cns ExtSlc₁ i)
      → (θ : (p : Pos ExtSlc₁ σ) → X₁ (Typ ExtSlc₁ σ p))
      → X₂ ((i , –> (next-ob≃ i) (slc-idx i σ (λ p → <– (next-ob≃ (Typ ExtSlc₁ σ p)) (θ p)))) , (σ , θ))
    next-witness = {!!}

