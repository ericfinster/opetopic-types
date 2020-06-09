{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import Pb

module OpetopicType where

  --
  --  The definition of opetopic type
  --

  record OpetopicType (M : 𝕄) : Set₁ where
    coinductive
    field
    
      Ob : Idx M → Set
      Hom : OpetopicType (Slice (Pb M Ob))

  open OpetopicType public

  action : (M : 𝕄) (A : Idx M → Set) → Set
  action M A = (f : Idx M) (σ : Cns M f)
    → (ν : (p : Pos M σ) → A (Typ M σ p))
    → A f 

  unique-action : (M : 𝕄) (A : Idx M → Set)
    → (W : Idx (Slice (Pb M A)) → Set)
    → Set
  unique-action M A W = (f : Idx M) (σ : Cns M f)
    → (ν : (p : Pos M σ) → A (Typ M σ p))
    → is-contr (Σ (A f) (λ a → W ((f , a) , σ , ν)))
    
  record is-fibrant {M : 𝕄} (X : OpetopicType M) : Set where
    coinductive
    field

      base-fibrant : unique-action M (Ob X) (Ob (Hom X))
      hom-fibrant : is-fibrant (Hom X)

  open is-fibrant public

  -- The terminal opetopic type.
  Terminal : (M : 𝕄) → OpetopicType M
  Ob (Terminal M) = cst ⊤
  Hom (Terminal M) = Terminal (Slice (Pb M (cst ⊤)))
  
  -- Relative opetopic types
  record OpetopicTypeOver {M : 𝕄} (M↓ : 𝕄↓ M) (X : OpetopicType M) : Set₁ where
    coinductive
    field

      Ob↓ : (i : Idx M) → Idx↓ M↓ i → Ob X i → Set
      Hom↓ : OpetopicTypeOver (Slice↓ (Pb↓ M↓ (Ob X) Ob↓)) (Hom X) 

  open OpetopicTypeOver public

