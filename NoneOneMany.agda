{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Algebricity
open import Pb
open import Finitary
open import AlgEqvElim
open import FibEquiv

module NoneOneMany where

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓) (M-fin : is-finitary M) where

    open import SliceAlg M M↓ 
    open import SliceUnfold M 
    open ExtUnfold M↓

    module _ (X₂ : Rel₂ ↓Rel₁) (is-fib-X₂ : is-fib₂ X₂) (alg-fib : AlgFib M M↓ X₂ is-fib-X₂)
             (X₃ : Rel₃ X₂) (is-fib-X₃ : is-fib₃ X₃) where

      open AlgFib alg-fib
      open AlgStruct M M↓ (Idx↓ M↓) (↓Rel₁) X₂ is-fib-X₂

      module X₃-struct = AlgStruct ExtSlc₁ ExtSlc↓₁ ↓Rel₁ X₂ X₃ is-fib-X₃

      -- is-fin-disc (Pos M (fst c)) (M-fin (fst c))
      --   (record { P = λ p → is-node (ε p) ;
      --             P-is-prop = λ p → Trunc-level ;
      --             P-is-dec = λ p → slice-is-dec (ε p) })

      module NdLemmas
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
                → Typ↓ ExtSlc↓₁ (nd↓ {i↓ = j , idp} (c↓ , ν↓) δ↓ ε↓) p == ϕ p) where


        open DecPred
        
        ε-has-node : DecPred (Pos M c) 
        P ε-has-node p = is-node (ε p)
        P-is-prop ε-has-node p = Trunc-level
        P-is-dec ε-has-node p = slice-is-dec (ε p)
        
        ε-form : SomeOrNone (Pos M c) ε-has-node
        ε-form = is-fin-disc (Pos M c) (M-fin c) ε-has-node 

        Goal : Set
        Goal = X₂ ((((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ) ,
                    ((j , idp) , μ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) δ↓)) ,
                    nd (c , ν) δ ε , ϕ) 

        corolla-case : (ε-is-lf : (p : Pos M c) → ¬ (is-node (ε p))) → Goal
        corolla-case no-nds = {!!} 

        binary-case : (ε-nd : Trunc ⟨-1⟩ (Σ (Pos M c) (λ p → is-node (ε p)))) → Goal
        binary-case nd-pos = {!!} 

        goal : Goal
        goal = Coprod-rec binary-case corolla-case ε-form

      -- alg-eqv-to : (i : Idx ExtSlc₂) → Idx↓ ExtSlc↓₂ i → X₂ i 
      -- alg-eqv-to ((((i , j) , ._ , ._) , (.j , idp) , ._ , ._) , lf .(i , j) , ϕ) ((._ , idp) , lf↓ .(j , idp) , ϕ↓) = {!!}
      -- alg-eqv-to ((((i , j) , ._ , ._) , (.j , idp) , ._ , ._) , nd (c , ν) δ ε , ϕ) ((._ , idp) , nd↓ (c↓ , ν↓) δ↓ ε↓ , ϕ↓) =  {!!} 
        -- transport X₂ claim (X₃-struct.ηX ((i , j) , c , ν) (ϕ (inl unit)))
        
        -- where open IdxIh i j c ν δ ε ϕ

        --       claim : ((((i , j) , c , ν) , ϕ true) , η ExtPlbk₂ (((i , j) , c , ν) , ϕ true)) ==
        --               ((((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ) , (j , idp) , μ↓ ExtPlbk↓₁ {i↓ = (j , idp)} (c↓ , ν↓) δ↓) , nd (c , ν) δ ε , ϕ)
        --       claim = pair= {!!} {!!} 

      -- postulate
      --   alg-eqv-to : (i : Idx ExtSlc₂) → Idx↓ ExtSlc↓₂ i → X₂ i 
      --   alg-eqv-is-equiv : (i : Idx ExtSlc₂) → is-equiv (alg-eqv-to i)
  
      -- alg-eqv : AlgEqv ExtSlc₁ ExtSlc↓₁ X₂ X₃ is-fib-X₃
      -- AlgEqv.e alg-eqv i = alg-eqv-to i , alg-eqv-is-equiv i
      -- AlgEqv.η-hyp alg-eqv (((i , j) , c , ν) , (j , idp) , (c↓ , ν↓)) (._ , idp) = {!!}

      --   -- So. The proof here is that when ϕ is instantiated with a constant function
      --   -- at the value give, then the "claim" equality from above evaluates to the
      --   -- identity.  So we have to think about how to set this up as nicely as possible
      --   -- so that this is true.

      --   -- You should check with the given hypotheses that the endpoints are already
      --   -- definitionally equal so that this has a chance of being true ...  but, yeah,
      --   -- that's going to be the idea.

      -- AlgEqv.μ-hyp alg-eqv i σ δ i↓ σ↓ δ↓ = {!!}

