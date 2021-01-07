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


    module _ (X₂ : Rel₂ ↓Rel₁) (is-fib-X₂ : is-fib₂ X₂)
             (X₃ : Rel₃ X₂) (is-fib-X₃ : is-fib₃ X₃) where

      postulate

        η-hyp : (i : Idx M) (j : Idx↓ M↓ i)
          → (ϕ : (p : Pos ExtSlc₁ (lf (i , j))) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ (lf (i , j)) p))
          → X₂ ((((i , j) , η M i , cst j) , (j , idp) , η↓ M↓ j , cst idp) , lf (i , j) , ϕ) 

        μ-hyp : (i : Idx M) (j : Idx↓ M↓ i)
          → (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
          → (δ : (p : Pos ExtPlbk₁ {i = i , j} (c , ν)) → Cns ExtPlbk₁ (Typ ExtPlbk₁ {i = i , j} (c , ν) p))
          → (ε : (p : Pos ExtPlbk₁ {i = i , j} (c , ν)) → Cns ExtSlc₁ (Typ ExtPlbk₁ {i = i , j} (c , ν) p , δ p))
          → (ϕ : (p : Pos ExtSlc₁ (nd {i = i , j} (c , ν) δ ε)) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ (nd {i = i , j} (c , ν) δ ε) p))
          → X₂ {!!}

      X₃-lf : (i : Idx ExtSlc₁) (j : Idx↓ ExtSlc↓₁ i)
        → X₂ ((i , j) , η ExtPlbk₂ (i , j))
      X₃-lf i j = fst (contr-center (is-fib-X₃ ((i , j) , η ExtPlbk₂ (i , j)) (lf (i , j)) ⊥-elim)) 

      -- This should simplify more ....
      
      -- nd (snd i)
      -- (λ p → η M (Typ M (fst (snd i)) p) , (λ _ → snd (snd i) p))
      -- (λ p → lf (Typ M (fst (snd i)) p , snd (snd i) p))
      -- , (λ _ → j)

      -- X₃-lf : (i : Idx M) (j j' : Idx↓ M↓ i) (j'=j : j' == j) (c : Cns M i)
      --   → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      --   → (d : Cns↓ M↓ j' c) (typ-d=ν : (p : Pos M c) → Typ↓ M↓ d p == ν p)
      --   → X₂ ((((i , j) , (c , ν)) , (j' , j'=j) , (d , typ-d=ν)) ,
      --        nd (c , ν) (λ p → η M (Typ M c p) , cst (ν p))
      --                   (λ p → lf (Typ M c p , ν p)) , {!!}) 
      -- X₃-lf = {!!} 

      -- What we will also need is that, under the above induced
      -- equivalence, the "unit" *use* X₃'s lf hypothesis.
        
      goal : (i : Idx ExtSlc₁) (σ : Cns ExtSlc₁ i)
        → (ϕ : (p : Pos ExtSlc₁ σ) → Idx↓ ExtSlc↓₁ (Typ ExtSlc₁ σ p))
        → X₂ ((i , slc-idx i σ ϕ) , σ , ϕ) 
      goal ((i , j) , ._ , ._) (lf .(i , j)) ϕ = η-hyp i j ϕ
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

