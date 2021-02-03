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

    module Fibs (X₂ : Rel₂ ↓Rel₁) (is-fib-X₂ : is-fib₂ X₂) (alg-fib : AlgFib M M↓ X₂ is-fib-X₂)
                (X₃ : Rel₃ X₂) (is-fib-X₃ : is-fib₃ X₃) where

      open AlgFib alg-fib

      module X₂-struct = AlgStruct M M↓ (Idx↓ M↓) (↓Rel₁) X₂ is-fib-X₂
      module X₃-struct = AlgStruct ExtSlc₁ ExtSlc↓₁ ↓Rel₁ X₂ X₃ is-fib-X₃

      alg-eqv-to : (i : Idx ExtSlc₂) → Idx↓ ExtSlc↓₂ i → X₂ i 

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

        GoalIdx : Idx ExtSlc₂
        GoalIdx = ((((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ) ,
                    ((j , idp) , μ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) δ↓)) ,
                    nd (c , ν) δ ε , ϕ)
                    
        Goal : Set
        Goal = X₂ GoalIdx 

        module IsCorolla (ε-is-lf : (p : Pos M c) → ¬ (is-node (ε p))) where

          CorollaIdx : Idx ExtSlc₂
          CorollaIdx = ((((i , j) , c , ν) , ϕ true) ,
                         η ExtPlbk₂ (((i , j) , c , ν) ,
                         ϕ true))

          CorollaX₂ : X₂ CorollaIdx
          CorollaX₂ = X₃-struct.ηX ((i , j) , c , ν) (ϕ (inl unit))
                       
          postulate

            corolla= : CorollaIdx == GoalIdx

          corolla-case : Goal
          corolla-case = transport X₂ corolla= CorollaX₂ 

        module HasDescendent (ε-nd : Trunc ⟨-1⟩ (Σ (Pos M c) (λ p → is-node (ε p)))) where

          -- Here are the elements we get from the induction hypothesis.
          descendant-ih-idx : (p : Pos M c) → Idx ExtSlc₂
          descendant-ih-idx p = (((Typ M c p , ν p) , δ p) ,
                                  (Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p) ,
                                   ε p , λ q → ϕ (inr (p , q)) 

          descendant-ih : (p : Pos M c) → X₂ (descendant-ih-idx p)
          descendant-ih p = alg-eqv-to (descendant-ih-idx p)
            ((((Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p) , idp) , ε↓ p , λ q → ϕ↓ (inr (p , q)))

          --
          --  Arguments to X₃-struct.μX
          --

          desc-i : Idx ExtSlc₁
          desc-i = ((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ)

          desc-c : Cns ExtSlc₁ desc-i
          desc-c = X₂-struct.μX-tr i c ν δ j ((j , idp) , c↓ , ν↓) (λ p → (Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p)

          desc-ν : (p : Pos ExtSlc₁ desc-c) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ desc-c p)
          desc-ν = X₂-struct.θX i c ν δ j ((j , idp) , c↓ , ν↓) (λ p → (Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p)

          desc-δ : (p : Pos ExtSlc₁ desc-c) → Cns ExtPlbk₂ (Typ ExtSlc₁ desc-c p , desc-ν p)
          desc-δ true = η ExtSlc₁ ((i , j) , c , ν) , η-dec ExtSlc₁ (Idx↓ ExtSlc↓₁) (ϕ true) 
          desc-δ (inr (p , true)) = ε p , λ q' → ϕ (inr (p , q')) 

          desc-x₀ : Idx↓ ExtSlc↓₁ ((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ)
          desc-x₀ = X₂-struct.μX i c ν δ j ((j , idp) , c↓ , ν↓) (λ p → (Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p)

          desc-x₁ : X₂ ((desc-i , desc-x₀) , desc-c , desc-ν)
          desc-x₁ = X₂-struct.μX-fill i c ν δ j ((j , idp) , c↓ , ν↓) (λ p → (Typ↓ M↓ c↓ p , ν↓ p) , δ↓ p)

          desc-δ↓ : (p : Pos ExtSlc₁ desc-c) → X₂ ((Typ ExtSlc₁ desc-c p , desc-ν p) , desc-δ p)
          desc-δ↓ true = transport! (λ h → X₂ ((((i , j) , c , ν) , h) , desc-δ true ))
                                    (ϕ↓ (inl unit)) (X₃-struct.ηX ((i , j) , c , ν) (ϕ true))
          desc-δ↓ (inr (p , true)) = descendant-ih p


          postulate

            -- The actual definition here takes a super long time to typecheck ...
            descendant-μ : X₂ ((((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ) , desc-x₀) ,
                                    μ ExtPlbk₂ {i = desc-i , desc-x₀} (desc-c , desc-ν) desc-δ)
            -- descendant-μ = X₃-struct.μX desc-i desc-c desc-ν desc-δ
            --                             desc-x₀ desc-x₁ desc-δ↓

            -- This should be true generically because of the form of the substitution.
            -- Question: do we need to use that there is a non-trivial attachment to make this true?
            desc-nd-eq : (nd (c , ν) δ ε , ϕ) == μ ExtPlbk₂ {i = desc-i , desc-x₀} (desc-c , desc-ν) desc-δ

          from-nd-hyp : (j , idp) , μ↓ ExtPlbk↓₁ {i↓ = j , idp} (c↓ , ν↓) δ↓ == desc-x₀
          from-nd-hyp = nd-hyp (i , j) (c , ν) δ (j , idp) (c↓ , ν↓) δ↓

          descendant-case : Goal
          descendant-case = transport! (λ h → X₂ ((((i , j) , μ ExtPlbk₁ {i = i , j} (c , ν) δ) , fst h) , snd h))
                                      (pair×= from-nd-hyp desc-nd-eq) descendant-μ 

        goal : Goal
        goal = Coprod-rec HasDescendent.descendant-case
                          IsCorolla.corolla-case ε-form


      -- alg-eqv-to : (i : Idx ExtSlc₂) → Idx↓ ExtSlc↓₂ i → X₂ i 
      alg-eqv-to ((((i , j) , ._ , ._) , (.j , idp) , ._ , ._) , lf .(i , j) , ϕ) ((._ , idp) , lf↓ .(j , idp) , ϕ↓) =
        transport! (λ h → X₂ ((iₛ , h) , lf (i , j) , ϕ)) jₛ=jₛ' (snd (contr-center (is-fib-X₂ iₛ (lf (i , j)) ϕ)))

        where iₛ : Idx ExtSlc₁
              iₛ = (i , j) , η M i , η-dec M (Idx↓ M↓) j

              jₛ : Idx↓ ExtSlc↓₁ iₛ
              jₛ = (j , idp) , (η↓ M↓ j , η↓-dec M↓ (λ i j k → j == k) idp)

              jₛ' : Idx↓ ExtSlc↓₁ iₛ
              jₛ' = fst (contr-center (is-fib-X₂ iₛ (lf (i , j)) ϕ))

              jₛ=jₛ' : jₛ == jₛ'
              jₛ=jₛ' = lf-hyp (i , j) (j , idp) ∙
                       -- have to fix the fact that ϕ ≠ ⊥-elim definitionally ...
                       ap (λ h → fst (contr-center (is-fib-X₂ iₛ (lf (i , j)) h))) (λ= (λ { () })) 

      alg-eqv-to ((((i , j) , ._ , ._) , (.j , idp) , ._ , ._) , nd (c , ν) δ ε , ϕ) ((._ , idp) , nd↓ (c↓ , ν↓) δ↓ ε↓ , ϕ↓) = goal
        where open NdLemmas i j c ν δ ε ϕ c↓ ν↓ δ↓ ε↓ ϕ↓ 

      postulate
      
        alg-eqv-is-equiv : (i : Idx ExtSlc₂) → is-equiv (alg-eqv-to i)
  
      -- alg-eqv : AlgEqv ExtSlc₁ ExtSlc↓₁ X₂ X₃ is-fib-X₃
      -- AlgEqv.e alg-eqv i = alg-eqv-to i , alg-eqv-is-equiv i
      -- AlgEqv.η-hyp alg-eqv (((i , j) , c , ν) , (j , idp) , (c↓ , ν↓)) (._ , idp) = {!!}
      -- AlgEqv.μ-hyp alg-eqv (._ , snd₂) (lf i , snd₁) δ i↓ (fst₁ , snd₃) δ↓ = {!!}
      -- AlgEqv.μ-hyp alg-eqv (._ , snd₂) (nd c δ₁ ε , snd₁) δ i↓ σ↓ δ↓ = {!!}

