{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
-- open import OpetopicType
-- open import IdentityMonad
-- open import IdentityMonadOver
-- open import InftyGroupoid
-- open import FundamentalThm
-- open import MonadEqv 

module SlcUnique where

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) (is-alg : is-algebraic M M↓) where

    Plbk : 𝕄
    Plbk = Pb M (Idx↓ M↓)

    Plbk↓ : 𝕄↓ Plbk
    Plbk↓ = Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)
    
    Slc : 𝕄
    Slc = Slice Plbk

    Slc↓ : 𝕄↓ Slc
    Slc↓ = Slice↓ Plbk↓

    DblSlc : 𝕄
    DblSlc = Slice (Pb Slc (Idx↓ Slc↓)) 

    DblSlc↓ : 𝕄↓ DblSlc
    DblSlc↓ = Slice↓ (Pb↓ Slc↓ (Idx↓ Slc↓) (λ i j k → j == k))
    
    CanonRel : Idx DblSlc → Set
    CanonRel = Idx↓ DblSlc↓ 

    module _ (R : Idx DblSlc → Set) where
    
      need-to-show : (i : Idx DblSlc) → R i ≃ CanonRel i
      need-to-show ((((i , j) , (c , ν)) , ((.j , idp) , (d , typ-d=ν))) , (ω , θ)) =
        {!θ!} 

      --
      -- CanonRel ((((i , j) , (c , ν)) , ((j , idp) , (d , typ-d=ν))) , (ω , θ)) reduces to:
      -- 
      -- Σ
      -- (Σ
      --  (Σ (Σ (Idx↓ M↓ i) (λ j₁ → j₁ == j))
      --   (λ i↓ →
      --      Σ (Cns↓ M↓ (fst i↓) c)
      --      (λ d₁ → (p : Pos M c) → Typ↓ M↓ d₁ p == ν p)))
      --  (λ j₁ → j₁ == (j , idp) , d , typ-d=ν))
      -- (λ i↓ →
      --    Σ
      --    (Pd↓ (Pb↓ M↓ (Idx↓ M↓) (λ i₁ → _==_)) (fst (fst i↓) , snd (fst i↓))
      --     ω)
      --    (λ d₁ →
      --       (p : Posₛ (Pb M (Idx↓ M↓)) ω) →
      --       Typ↓ₛ (Pb↓ M↓ (Idx↓ M↓) (λ i₁ → _==_)) d₁ p == θ p))

      
