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

      module NdCases
          (i : Idx M)
          (j : Idx↓ M↓ i) (c : Cns M i)
          (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
          (δ : (p : Pos ExtPlbk₁ {i = i , j} (c , ν))
               → Cns ExtPlbk₁ (Typ ExtPlbk₁ {i = i , j} (c , ν) p))
          (ε : (p : Pos ExtPlbk₁ {i = i , j} (c , ν))
               → Cns ExtSlc₁ (Typ ExtPlbk₁ {i = i , j} (c , ν) p , δ p)) 
          (ϕ : (p : Pos ExtSlc₁ (nd {i = i , j} (c , ν) δ ε))
               → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ (nd {i = i , j} (c , ν) δ ε) p)) 
          (c↓ : Cns↓ M↓ j c)
          (ν↓ : (p : Pos M c) → Typ↓ M↓ c↓ p == ν p) 
          (δ↓ : (p : Pos M c) → Cns↓ ExtPlbk↓₁ (Typ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) p) (δ p)) 
          (ε↓ : (p : Pos M c) → Cns↓ ExtSlc↓₁ (Typ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) p , δ↓ p) (ε p))
          (ϕ↓ : (p : Pos ExtSlc₁ (nd {i = i , j} (c , ν) δ ε))
                → Typ↓ ExtSlc↓₁ (nd↓ {i↓ = j , idp} (c↓ , ν↓) δ↓ ε↓) p == ϕ p)
          (κ : (p : Pos ExtPlbk₂ {i = _ , (j , idp) , μ↓ ExtPlbk↓₁ {i↓ = j , idp } (c↓ , ν↓) δ↓} (nd {i = i , j} (c , ν) δ ε , ϕ))
               → Cns ExtPlbk₂ (Typ ExtPlbk₂ {i = _ , (j , idp) , μ↓ ExtPlbk↓₁ {i↓ = j , idp } (c↓ , ν↓) δ↓} (nd {i = i , j} (c , ν) δ ε , ϕ) p))
          (κ↓ : (p : Pos ExtPlbk₂ {i = _ , (j , idp) , μ↓ ExtPlbk↓₁ {i↓ = j , idp } (c↓ , ν↓) δ↓} (nd {i = i , j} (c , ν) δ ε , ϕ)) 
                → Cns↓ ExtPlbk↓₂ (Typ↓ ExtPlbk↓₂ {i↓ = ((j , idp) , μ↓ ExtPlbk↓₁ {i↓ = j , idp } (c↓ , ν↓) δ↓) , idp} (nd↓ {i↓ = j , idp} (c↓ , ν↓) δ↓ ε↓ , ϕ↓) p) (κ p)) where 

        open NdLemmas i j c ν δ ε ϕ c↓ ν↓ δ↓ ε↓ ϕ↓
        
        iₛ : Idx ExtSlc₁
        iₛ = (i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ

        jₛ : Idx↓ ExtSlc↓₁ iₛ
        jₛ = (j , idp) , μ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) δ↓
        
        postulate
        
          we-need : alg-eqv-to ((iₛ , jₛ) , (μ ExtPlbk₂ {i = iₛ , jₛ} (nd (c , ν) δ ε , ϕ) κ))  -- the μ computes
                               ((jₛ , idp) , (μ↓ ExtPlbk↓₂ {i↓ = jₛ , idp} (nd↓ {i↓ = j , idp} (c↓ , ν↓) δ↓ ε↓ , ϕ↓) κ↓)) ==  -- the μ↓ computes
                    X₃-struct.μX iₛ (nd {i = i , j} (c , ν) δ ε) ϕ κ jₛ goal
                      -- (alg-eqv-to ((iₛ , jₛ) , nd (c , ν) δ ε , ϕ) ((jₛ , idp) , (nd↓ {i↓ = j , idp} (c↓ , ν↓) δ↓ ε↓ , ϕ↓)))  -- this computes to "goal" in NdLemmas
                      (λ p → alg-eqv-to (Typ ExtPlbk₂ {i = iₛ , jₛ} (nd (c , ν) δ ε , ϕ) p , κ p)
                                        (Typ↓ ExtPlbk↓₂ {i↓ = jₛ , idp} (nd↓ {i↓ = j , idp} (c↓ , ν↓) δ↓ ε↓ , ϕ↓) p , κ↓ p))


          -- okay. so. what we see quite immediately is that the two mu's are going to compute.
          -- good. so now. this means that in order to get "goal" to reduce, we'll need to prove this
          -- using a coproduct elim.  and we'll have one thing to prove in each case.

          -- corolla case: the decorations κ/κ↓ are determined by their value on this unique node.
          -- and so we just need to know that μX₃ is like, unital at the base element

          -- many case: we'll have an induction hypothesis. and we'll
          -- have to prove that alg-eqv is somehow compatible with γ.
          -- why should this be?  we'll, I mean, I think the reason is
          -- clear: it should be because the values of alg-eqv-to are
          -- calculated by applying μX₃.  And *this* multiplication is
          -- unital and associative provided it extends once more.

          -- but what exactly is the *statement* which says in which sense it is compatible with γ?

      -- alg-eqv : AlgEqv ExtSlc₁ ExtSlc↓₁ X₂ X₃ is-fib-X₃
      -- AlgEqv.e alg-eqv i = alg-eqv-to i , alg-eqv-is-equiv i
      -- AlgEqv.η-hyp alg-eqv (((i , j) , c , ν) , (j , idp) , (c↓ , ν↓)) (._ , idp) = {!!}
      -- AlgEqv.μ-hyp alg-eqv (._ , ._) (lf (i , j) , ϕ) κ (((.j , idp) , ._ , ._) , idp) (lf↓ .(j , idp) , ϕ↓) κ↓ = {!!}
      -- AlgEqv.μ-hyp alg-eqv (._ , ._) (nd {i = i , j} (c , ν) δ ε , ϕ) κ (((.j , idp) , ._ , ._) , idp) (nd↓ (c↓ , ν↓) δ↓ ε↓ , ϕ↓) κ↓ = we-need
      --   where open NdCases i j c ν δ ε ϕ c↓ ν↓ δ↓ ε↓ ϕ↓ κ κ↓ 

