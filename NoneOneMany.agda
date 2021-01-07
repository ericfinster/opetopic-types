{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import Finitary
open import AlgEqvElim

module NoneOneMany where

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓) (M-fin : is-finitary M) where

    open import SliceAlg M M↓ 
    open import SliceUnfold M 
    open ExtUnfold M↓

    module Reductions where
    
      lf-red₀ : (i : Idx ExtSlc₁) (σ : Cns ExtSlc₁ i)
        → (ϕ : (p : Pos ExtSlc₁ σ) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ σ p))
        → (is-lf : is-leaf σ)
        → η (Pb M (Idx↓ M↓)) (fst i) == snd i 
      lf-red₀ ._ (lf i) ϕ is-lf = idp
      lf-red₀ ._ (nd c δ ε) ϕ is-lf = ⊥-rec (is-lf [ inl unit ])

      lf-red : (i : Idx ExtSlc₁) (σ : Cns ExtSlc₁ i)
        → (ϕ : (p : Pos ExtSlc₁ σ) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ σ p))
        → (is-lf : is-leaf σ)
        → slc-idx i σ ϕ == (snd (fst i) , idp) ,
          transport (λ x → Cns↓ ExtPlbk↓₁ (snd (fst i) , idp) x)
                    (lf-red₀ i σ ϕ is-lf) (η↓ ExtPlbk↓₁ (snd (fst i) , idp))
      lf-red ._ (lf i) ϕ is-lf = idp
      lf-red ._ (nd c δ ε) ϕ is-lf = ⊥-rec (is-lf [ inl unit ])


    module _ (X₂ : Rel₂ ↓Rel₁) (is-fib-X₂ : is-fib₂ X₂) (alg-fib : AlgFib M M↓ X₂ is-fib-X₂)
             (X₃ : Rel₃ X₂) (is-fib-X₃ : is-fib₃ X₃) where

      open AlgFib alg-fib
      open AlgStruct M M↓ (Idx↓ M↓) (↓Rel₁) X₂ is-fib-X₂
      
      --
      --  These are our hypotheses ...
      --

      --   lf-hyp : (i : Idx ExtPlbk₁) (j : Idx↓ ExtPlbk↓₁ i)
      --     → (j , η↓ ExtPlbk↓₁ j) == ηX (fst i) (snd i)

      --   nd-hyp : (i : Idx ExtPlbk₁) (c : Cns ExtPlbk₁ i)
      --     → (δ : (p : Pos ExtPlbk₁ {i = i} c) → Cns ExtPlbk₁ (Typ ExtPlbk₁ {i = i} c p))
      --     → (j : Idx↓ ExtPlbk↓₁ i) (d : Cns↓ ExtPlbk↓₁ j c)
      --     → (δ↓ : (p : Pos ExtPlbk₁ {i = i} c) → Cns↓ ExtPlbk↓₁ (Typ↓ ExtPlbk↓₁ {i↓ = j} d p) (δ p))
      --     → (j , μ↓ ExtPlbk↓₁ {i↓ = j} d δ↓)
      --       == μX (fst i) (fst c) (snd c) δ (snd i) (j , d)
      --             (λ p → (Typ↓ M↓ (fst d) p , snd d p) , δ↓ p)

      X₃-lf : (i : Idx ExtSlc₁) (j : Idx↓ ExtSlc↓₁ i)
        → X₂ ((i , j) , η ExtPlbk₂ (i , j))
      X₃-lf i j = fst (contr-center (is-fib-X₃ ((i , j) , η ExtPlbk₂ (i , j)) (lf (i , j)) ⊥-elim)) 

      -- This can probably be cleaned up a bit ...
      η-wit : (i : Idx M) (j : Idx↓ M↓ i)
        → (ϕ : (p : Pos ExtSlc₁ (lf (i , j))) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ (lf (i , j)) p))
        → X₂ ((((i , j) , η M i , cst j) , (j , idp) , η↓ M↓ j , cst idp) , lf (i , j) , ϕ) 
      η-wit i j ϕ = transport X₂ pth (snd (contr-center (is-fib-X₂ ((i , j) , η M i , cst j) (lf (i , j)) ⊥-elim)))  

        where pth : (((i , j) , η M i , (λ _ → j)) , ηX i j) , lf (i , j) , ⊥-elim ==
                    (((i , j) , η M i , cst j) , (j , idp) , η↓ M↓ j , cst idp) , lf (i , j) , ϕ
              pth =   ap (λ x → (((i , j) , η M i , (λ _ → j)) , x) , lf (i , j) , ⊥-elim) (! (lf-hyp (i , j) (j , idp))) ∙
                      ap (λ x → (((i , j) , η M i , cst j) , (j , idp) , η↓ M↓ j , cst idp) , lf (i , j) , x) (λ= (λ { () }))


      goal : (i : Idx ExtSlc₁) (σ : Cns ExtSlc₁ i)
        → (ϕ : (p : Pos ExtSlc₁ σ) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ σ p))
        → X₂ ((i , slc-idx i σ ϕ) , σ , ϕ) 
      goal ((i , j) , ._ , ._) (lf .(i , j)) ϕ = η-wit i j ϕ
      goal ((i , j) , ._ , ._) (nd c δ ε) ϕ with is-fin-disc (Pos M (fst c)) (M-fin (fst c))
        (record { P = λ p → is-node (ε p) ;
                  P-is-prop = λ p → Trunc-level ;
                  P-is-dec = λ p → slice-is-dec (ε p) })
      goal ((i , j) , .(μ M (fst c) (fst ∘ δ)) , _) (nd c δ ε) ϕ | inl p = {!!} -- The multi-valued case
      goal ((i , j) , .(μ M c (fst ∘ δ)) , _) (nd (c , ν) δ ε) ϕ | inr ¬p = {!ϕ true!} -- The corolla case

        where open IdxIh i j c ν δ ε ϕ

              have : X₂ ((((i , j) , c , ν) , ϕ true) , η ExtPlbk₂ (((i , j) , c , ν) , ϕ true))
              have = X₃-lf ((i , j) , c , ν) (ϕ (inl unit))
              
              need : X₂ ((((i , j) , μ M c (fst ∘ δ) , _) , (j' , j'=j) , (μ↓ M↓ d δ↓' , typ-μ↓=ν')) , nd (c , ν) δ ε , ϕ)
              need = {!!} 

      alg-eqv : AlgEqv ExtSlc₁ ExtSlc↓₁ X₂ X₃ is-fib-X₃
      AlgEqv.e alg-eqv = {!!}
      AlgEqv.η-hyp alg-eqv = {!!}
      AlgEqv.μ-hyp alg-eqv = {!!}

