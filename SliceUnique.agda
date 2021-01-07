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

  -- The unit and multiplication induced by a fibrant 2-relation
  module AlgStruct (M : 𝕄) (X₀ : Rel₀ M) (X₁ : Rel₁ M X₀)
                   (X₂ : Rel₂ M X₁) (is-fib-X₂ : is-fib₂ M X₂) where

    ηX : (i : Idx M) (x₀ : X₀ i)
      → X₁ ((i , x₀) , η M i , cst x₀)
    ηX i x₀ = fst (contr-center (is-fib-X₂ ((i , x₀) , η M i , cst x₀) (lf (i , x₀)) ⊥-elim)) 


    module _ (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → X₀ (Typ M c p))
             (δ : (p : Pos M c) → Cns (Pb M X₀) (Typ M c p , ν p))
             (x₀ : X₀ i) (x₁ : X₁ ((i , x₀) , c , ν))
             (δ↓ : (p : Pos M c) → X₁ ((Typ M c p , ν p) , (δ p))) where
             
      μX-tr : Pd (Pb M X₀) ((i , x₀) , μ (Pb M X₀) {i = i , x₀} (c , ν) δ)
      μX-tr = nd (c , ν) δ (λ p →
              nd (δ p) (λ q → η (Pb M X₀) (Typ (Pb M X₀) {i = Typ M c p , ν p} (δ p) q)) (λ q →
              lf (Typ (Pb M X₀) {i = Typ M c p , ν p} (δ p) q)))

      θX : (p : Pos (Slice (Pb M X₀)) μX-tr) → X₁ (Typ (Slice (Pb M X₀)) μX-tr p)
      θX true = x₁
      θX (inr (p , true)) = δ↓ p

      μX : X₁ ((i , x₀) , μ (Pb M X₀) {i = i , x₀} (c , ν) δ)
      μX = fst (contr-center (is-fib-X₂ ((i , x₀) , μ (Pb M X₀) {i = i , x₀} (c , ν) δ) μX-tr θX))


  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (X₁ : Rel₁ M (Idx↓ M↓)) where

    

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (X₁ : Rel₁ M (Idx↓ M↓))
           (X₂ : Rel₂ M X₁) (is-fib-X₂ : is-fib₂ M X₂)
            where

    open ExtUnfold M M↓
    open AlgStruct M (Idx↓ M↓) X₁ X₂ is-fib-X₂

    record AlgEqv : Set where
      field 

        eqv : (i : Idx ExtSlc₁) → X₁ i ≃ Idx↓ ExtSlc↓₁ i

        preserves-η : (i : Idx M) (j : Idx↓ M↓ i)
          → –> (eqv ((i , j) , η M i , cst j)) (ηX i j)
          == (j , idp) , η↓ M↓ j , cst idp  
          
        preserves-μ : (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
          → (δ : (p : Pos M c) → Cns (Pb M (Idx↓ M↓)) (Typ M c p , ν p))
          → (j : Idx↓ M↓ i) (x₁ : X₁ ((i , j) , c , ν))
          → (δ↓ : (p : Pos M c) → X₁ ((Typ M c p , ν p) , (δ p))) → 
          let ω = (–> (eqv ((i , j) , c , ν)) x₁)
          in –> (eqv ((i , j) , μ (Pb M (Idx↓ M↓)) {i = i , j} (c , ν) δ)) (μX i c ν δ j x₁ δ↓)
          
             == (fst ω , μ↓ M↓ {δ = fst ∘ δ} (fst (snd ω))
                  (λ p → transport (λ x → Cns↓ M↓ x (fst (δ p))) (snd (fst (–> (eqv ((Typ M c p , ν p) , δ p)) (δ↓ p))) ∙ ! (snd (snd ω) p))
                         (fst (snd (–> (eqv ((Typ M c p , ν p) , δ p)) (δ↓ p))))) ,
                  (λ p → {!!})) 



