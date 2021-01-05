{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import Algebricity
open import SliceUnfold

module Sketch where

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓) where

    module WitEqv (X₁ : Rel₁ M (Idx↓ M↓)) (is-fib-X₁ : is-fib₁ M X₁)
             (X₁-is-alg : (i : Idx M) (c : Cns M i)
               → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
               → X₁ ((i , idx (contr-center (is-alg i c ν))) , c , ν)) where

      open ExtUnfold M M↓ 

      -- The above induces an equivalence by fibrancy
      wit-equiv : (i : Idx M) (j : Idx↓ M↓ i) (c : Cns M i)
          → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
          → X₁ ((i , j) , (c , ν)) ≃ ↓Rel₁ ((i , j) , (c , ν))
      wit-equiv i j c ν = equiv to from {!!} {!!} 

        where to : X₁ ((i , j) , c , ν) → ↓Rel₁ ((i , j) , c , ν)
              to x₁ = (idx α , fst= pth) , cns α , app= (typ α)

                where α : alg-comp M M↓ i c ν
                      α = contr-center (is-alg i c ν)

                      pth : (idx α , X₁-is-alg i c ν) == (j , x₁) 
                      pth = contr-has-all-paths ⦃ is-fib-X₁ i c ν ⦄ (idx α , X₁-is-alg i c ν) (j , x₁)

              from : ↓Rel₁ ((i , j) , c , ν) → X₁ ((i , j) , c , ν)
              from ((j' , j'=j) , d , t) = transport (λ x → X₁ ((i , x) , c , ν))
                (ap idx (contr-path (is-alg i c ν) α) ∙ j'=j) x₁ 

                where α : alg-comp M M↓ i c ν
                      α = ⟦ j' ∣ d ∣ λ= t ⟧ 

                      x₁ : X₁ ((i , idx (contr-center (is-alg i c ν))) , c , ν)
                      x₁ = X₁-is-alg i c ν

    module _ (X₁ : Rel₁ M (Idx↓ M↓)) (is-fib-X₁ : is-fib₁ M X₁)
             (X₁-is-alg : (i : Idx M) (c : Cns M i)
               → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
               → X₁ ((i , idx (contr-center (is-alg i c ν))) , c , ν))
             (X₂ : Rel₂ M X₁) (is-fib-X₂ : is-fib₂ M X₂) where

      open ExtUnfold M M↓ 
      open WitEqv X₁ is-fib-X₁ X₁-is-alg
      
      η-el : (i : Idx M) (j : Idx↓ M↓ i)
        → X₁ ((i , j) , η M i , cst j)
      η-el i j = <– (wit-equiv i j (η M i) (cst j)) ((j , idp) , η↓ M↓ j , cst idp) 

      -- wit-equiv : (i : Idx M) (j : Idx↓ M↓ i) (c : Cns M i)
      --     → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      --     → X₁ ((i , j) , (c , ν)) ≃ ↓Rel₁ ((i , j) , (c , ν))

      by-fib : (i : Idx M) (j : Idx↓ M↓ i)
        → Σ (X₁ ((i , j) , η M i , cst j))
          (λ x₁ → X₂ ((((i , j) , η M i , cst j) , x₁) , lf (i , j) , ⊥-elim))
      by-fib i j = contr-center (is-fib-X₂ ((i , j) , η M i , cst j) (lf (i , j)) ⊥-elim) 

      done-if : (i : Idx M) (j : Idx↓ M↓ i)
        → fst (by-fib i j) == η-el i j
      done-if i j = {!!} 

      -- from-ft : (i : Idx M) (j j' : Idx↓ M↓ i)
      --   → Σ (Cns↓ M↓ j' (η M i)) (λ d → Typ↓ M↓ d == cst j) ≃ (j == j')

      -- Now.  The goal is to show that we have a null-homotopy of
      -- the image of η under the above equivalence.
      goal : (i : Idx M) (j : Idx↓ M↓ i)
        → X₂ ((((i , j) , η M i , cst j) , η-el i j) , lf (i , j) , ⊥-elim)
      goal i j = transport (λ x → X₂ ((((i , j) , η M i , cst j) , x) , lf (i , j) , ⊥-elim))
                           (done-if i j) (snd (by-fib i j)) 
