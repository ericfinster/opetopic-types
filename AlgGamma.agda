{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Algebricity
open import Pb
open import Finitary
open import AlgEqvElim
open import NoneOneMany

module AlgGamma where

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓) (M-fin : is-finitary M) where

    open import SliceAlg M M↓ 
    open import SliceUnfold M 
    open ExtUnfold M↓

    module _ (X₂ : Rel₂ ↓Rel₁) (is-fib-X₂ : is-fib₂ X₂) (alg-fib : AlgFib M M↓ X₂ is-fib-X₂)
             (X₃ : Rel₃ X₂) (is-fib-X₃ : is-fib₃ X₃) where

      open AlgFib alg-fib

      open Fibs M M↓ is-alg M-fin X₂ is-fib-X₂ alg-fib X₃ is-fib-X₃

      module GammaComm
          (i : Idx M) (j : Idx↓ M↓ i)
          (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
          
          (δ : (p : Pos ExtPlbk₁ {i = i , j} (c , ν))
               → Cns ExtPlbk₁ (Typ ExtPlbk₁ {i = i , j} (c , ν) p))
          (ε : (p : Pos ExtPlbk₁ {i = i , j} (c , ν))
               → Cns ExtSlc₁ (Typ ExtPlbk₁ {i = i , j} (c , ν) p , δ p)) 
          
          (c↓ : Cns↓ M↓ j c) (ν↓ : (p : Pos M c) → Typ↓ M↓ c↓ p == ν p)
          (δ↓ : (p : Pos M c) → Cns↓ ExtPlbk↓₁ (Typ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) p) (δ p)) 
          (ε↓ : (p : Pos M c) → Cns↓ ExtSlc↓₁ (Typ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) p , δ↓ p) (ε p))
          
          (σ : Cns ExtSlc₁ ((i , j) , c , ν))
          (ϕ : (p : Pos ExtSlc₁ σ) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ σ p))
          (ψ : (p : Pos M c) (q : Pos ExtSlc₁ (ε p)) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ (ε p) q))

          (σ↓ : Cns↓ ExtSlc↓₁ ((j , idp) , c↓ , ν↓) σ)
          (ϕ↓ : (p : Pos ExtSlc₁ σ) → Typ↓ ExtSlc↓₁ σ↓ p == ϕ p)
          (ψ↓ : (p : Pos M c) (q : Pos ExtSlc₁ (ε p)) → Typ↓ ExtSlc↓₁ (ε↓ p) q == ψ p q)

          -- (ϕ : (p : Pos ExtSlc₁ (γ ExtPlbk₁ σ δ ε)) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ (γ ExtPlbk₁ σ δ ε) p))
          -- (ϕ↓ : (p : Pos ExtSlc₁ (γ ExtPlbk₁ σ δ ε)) → Typ↓ ExtSlc↓₁ (γ↓ ExtPlbk↓₁ σ↓ δ↓ ε↓) p == ϕ p)  where

          where
          
        iₛ : Idx ExtSlc₁
        iₛ = (i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ

        jₛ : Idx↓ ExtSlc↓₁ iₛ
        jₛ = (j , idp) , μ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) δ↓

        desc-i : Idx ExtSlc₁
        desc-i = ((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ)

        desc-c : Cns ExtSlc₁ desc-i
        desc-c = X₂-struct.μX-tr i c ν δ j ((j , idp) , c↓ , ν↓) (λ p → (Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p)

        desc-ν : (p : Pos ExtSlc₁ desc-c) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ desc-c p)
        desc-ν = X₂-struct.θX i c ν δ j ((j , idp) , c↓ , ν↓) (λ p → (Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p)

        desc-δ : (p : Pos ExtSlc₁ desc-c) → Cns ExtPlbk₂ (Typ ExtSlc₁ desc-c p , desc-ν p)
        desc-δ true = σ , ϕ 
        desc-δ (inr (p , true)) = ε p , λ q → ψ p q

        desc-x₀ : Idx↓ ExtSlc↓₁ ((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ)
        desc-x₀ = X₂-struct.μX i c ν δ j ((j , idp) , c↓ , ν↓) (λ p → (Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p)

        -- desc-x₁ : X₂ ((desc-i , desc-x₀) , desc-c , desc-ν)
        -- desc-x₁ = X₂-struct.μX-fill i c ν δ j ((j , idp) , c↓ , ν↓) (λ p → (Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p)

        desc-x₁ : X₂ ((desc-i , jₛ) , desc-c , desc-ν)
        desc-x₁ = alg-eqv-to ((desc-i , jₛ) , desc-c , desc-ν)
          ((jₛ , idp) , nd↓ (c↓ , ν↓) δ↓ (λ p → η↓ ExtSlc↓₁ (Typ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) p , δ↓ p)) ,
                        {!!})

        desc-δ↓ : (p : Pos ExtSlc₁ desc-c) → X₂ ((Typ ExtSlc₁ desc-c p , desc-ν p) , desc-δ p)
        desc-δ↓ true = alg-eqv-to ((((i , j) , c , ν) , desc-ν true) , σ , ϕ) ((((j , idp) , c↓ , ν↓) , idp) , σ↓ , ϕ↓)
        desc-δ↓ (inr (p , true)) = alg-eqv-to ((((Typ M c p , ν p) , δ p) , desc-ν (inr (p , true))) , ε p , ψ p)
                                              ((((Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p) , idp) , ε↓ p , ψ↓ p)


        postulate

          ϕψ : (p : Pos ExtSlc₁ (γ ExtPlbk₁ σ δ ε)) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ (γ ExtPlbk₁ σ δ ε) p)
          ϕψ↓ : (p : Pos ExtSlc₁ (γ ExtPlbk₁ σ δ ε)) → Typ↓ ExtSlc↓₁ (γ↓ ExtPlbk↓₁ σ↓ δ↓ ε↓) p == ϕψ p

          alg-eqv-γ : alg-eqv-to ((iₛ , jₛ) , γ ExtPlbk₁ σ δ ε , {!!})
                                 ((jₛ , idp) , γ↓ ExtPlbk↓₁ σ↓ δ↓ ε↓ , {!!}) ==
                      X₃-struct.μX desc-i desc-c desc-ν desc-δ
                                   jₛ desc-x₁ desc-δ↓ 

