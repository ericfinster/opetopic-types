{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb
open import OpetopicType

module Algebras where

  -- Here's my working definition of the opetopic type
  -- determined by a monad over.
  ↓-to-OpType : (M : 𝕄) (M↓ : 𝕄↓ M)
    → OpetopicType M
  Ob (↓-to-OpType M M↓) = Idx↓ M↓ 
  Hom (↓-to-OpType M M↓) =
    ↓-to-OpType (Slice (Pb M (Idx↓ M↓)))
                       (Slice↓ (Pb↓ M↓ (Idx↓ M↓) (λ i j k → j == k)))

  module _ (M : 𝕄) (M↓ : 𝕄↓ M) where

    record alg-comp (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p)) : Set where
      constructor ⟦_∣_∣_⟧
      field
        idx : Idx↓ M↓ i 
        cns : Cns↓ M↓ idx c
        typ : Typ↓ M↓ cns == ν

    is-algebraic : Set
    is-algebraic = (i : Idx M) (c : Cns M i)
      → (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → is-contr (alg-comp i c ν) 
    
    open alg-comp public

    alg-comp-= : (i : Idx M) (c : Cns M i) (ν : (p : Pos M c) → Idx↓ M↓ (Typ M c p))
      → {j j' : Idx↓ M↓ i} (m : j == j')
      → {d : Cns↓ M↓ j c} {d' : Cns↓ M↓ j' c}
      → (n : d == d' [ (λ x → Cns↓ M↓ x c) ↓ m ])
      → {r : Typ↓ M↓ d == ν} {r' : Typ↓ M↓ d' == ν}
      → (ϕ : (p : Pos M c) → app= r p == ap (λ x → Typ↓ M↓ (snd x) p) (pair= m n) ∙ app= r' p)
      → ⟦ j ∣ d ∣ r ⟧ == ⟦ j' ∣ d' ∣ r' ⟧
    alg-comp-= i c ν {j = j} idp {d = d} idp {r} {r'} ϕ =
      ap (λ x → ⟦ j ∣ d ∣ x ⟧) (λ=-η r ∙ ap λ= (λ= ϕ) ∙ ! (λ=-η r'))
