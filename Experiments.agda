{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType

module Experiments where

  -- Here's my working definition of the opetopic type
  -- determined by a monad over.
  OverToOpetopicType : (M : 𝕄) (M↓ : 𝕄↓ M) → OpetopicType M
  Ob (OverToOpetopicType M M↓) = Idx↓ M↓ 
  Hom (OverToOpetopicType M M↓) =
    OverToOpetopicType (Slice (Pb M (Idx↓ M↓)))
                       (Slice↓ (Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)))

  -- This should be a characterization of those monads which
  -- arise as the slice construction of an algebra.
  is-algebraic : (M : 𝕄) (M↓ : 𝕄↓ M) → Set
  is-algebraic M M↓ = (i : Idx M) (c : Cns M i)
    → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
    → is-contr (Σ (Idx↓ M↓ i) (λ j → Σ (Cns↓ M↓ j c) (λ d → Typ↓ M↓ d == ν))) 

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    record alg-comp (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p)) : Set where
      field
        idx : Idx↓ M↓ i 
        cns : Cns↓ M↓ idx c
        typ : Typ↓ M↓ cns == ν

    is-alg : Set
    is-alg = (i : Idx M) (c : Cns M i)
      → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → is-contr (alg-comp i c ν) 

  open alg-comp
  
  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    Slc : 𝕄
    Slc = Slice (Pb M (Idx↓ M↓))

    Slc↓ : 𝕄↓ Slc
    Slc↓ = Slice↓ (Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k))

    conj : is-alg Slc Slc↓ 
    conj ((i , j) , ._ , ._) (lf .(i , j)) ϕ = has-level-in (ctr , {!!})

      where ctr : alg-comp Slc Slc↓ ((i , j) , η M i , (λ _ → j)) (lf (i , j)) ϕ
            idx ctr = (j , idp) , (η↓ M↓ j , λ _ → idp)
            cns ctr = lf↓ {M↓ = Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)} (j , idp)
            typ ctr = {!!}

    -- Pd↓ (Pb↓ M↓ (Idx↓ M↓) (λ i₁ → _==_)) ((j , idp) , η↓ M↓ j , (λ _ → idp)) (lf (i , j))

    conj ((i , j) , ._ , ._) (nd σ δ ε) ϕ = {!!}

    -- So.  My possibly crazy conjecture is that after slicing, we
    -- always get an algebraic monad.  Let me just see if I think I
    -- believe it or not.  This actually looks reasonable.  I guess
    -- you will have to use som kind's of equality of trees or
    -- something, but the statement seems correct.  Let's just start.
