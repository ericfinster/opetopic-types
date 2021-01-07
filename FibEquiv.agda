{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver

module FibEquiv where

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓) where

    open import SliceUnfold M
    open ExtUnfold M↓
    
    module _ (X : Rel₁ (Idx↓ M↓)) (is-fib-X : is-fib₁ X)
             (X-is-alg : (i : Idx M) (c : Cns M i)
               → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
               → X ((i , idx (contr-center (is-alg i c ν)) ) , c , ν)) where

      fib-eqv : (i : Idx ExtSlc₁) → Idx↓ ExtSlc↓₁ i ≃ X i 
      fib-eqv ((i , j) , c , ν) = equiv to from to-from from-to 

        where to : Idx↓ ExtSlc↓₁ ((i , j) , c , ν) → X ((i , j) , c , ν)
              to ((j' , j'=j) , d , t) = transport (λ x → X ((i , x) , c , ν)) pth (X-is-alg i c ν) 

                where α : alg-comp M M↓ i c ν
                      α = ⟦ j' ∣ d ∣ λ= t ⟧ 

                      pth : idx (contr-center (is-alg i c ν)) == j
                      pth = ap idx (contr-path (is-alg i c ν) α) ∙ j'=j 

              from :  X ((i , j) , c , ν) → Idx↓ ExtSlc↓₁ ((i , j) , c , ν) 
              from x = (idx α , pth) , cns α , app= (typ α)

                where α : alg-comp M M↓ i c ν
                      α = contr-center (is-alg i c ν)

                      pth : idx α == j
                      pth = fst= (contr-has-all-paths ⦃ is-fib-X i c ν ⦄ (idx α , X-is-alg i c ν) (j , x))  

              to-from : (x : X ((i , j) , c , ν)) → to (from x) == x
              to-from x = {!!} 

              from-to : (a : Idx↓ ExtSlc↓₁ ((i , j) , c , ν)) → from (to a) == a
              from-to ((j' , j'=j) , d , t) = {!!} 
