{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver
open import IdentityMonad
open import Pb
open import OpetopicType
open import FundamentalThm

module Globular where

  record GType : Set₁ where
    coinductive
    field 
      GOb : Set 
      GHom : (x y : GOb) → GType

  open GType public

  TypeToGType : (X : Set) → GType
  GOb (TypeToGType X) = X
  GHom (TypeToGType X) x y = TypeToGType (x == y)

  OpetopicToGlobular : (M : 𝕄) (X : OpetopicType M) → Idx M → GType
  GOb (OpetopicToGlobular M X i) = Ob X i
  GHom (OpetopicToGlobular M X i) x y =
    OpetopicToGlobular (Slice (Pb M (Ob X))) (Hom X)
                       ((i , x) , (η M i , λ _ → y))
  
  -- Okay.  That looks right, yeah?  Indeed.  So, under what
  -- conditions can we be sure that applying this construction
  -- to an opetopic type in fact gives the identity guy.

  -- So, like, suppose an opetopic type is fibrant.  Is it then
  -- the case that the hom between two elements over η must be
  -- an identity type? 

  module _ (M : 𝕄) (X : OpetopicType M) (is-fib : is-fibrant X) where

    R : (i : Idx M) (x y : Ob X i) → Set
    R i x y = Ob (Hom X) ((i , y) , (η M i , λ _ → x)) 

    refl : (i : Idx M) (x : Ob X i) → R i x x
    refl i x = fst (contr-center (base-fibrant (hom-fibrant is-fib) ((i , x) , (η M i , cst x)) (lf (i , x)) ⊥-elim))

    -- Exactly.  So we get refl.  So it's reflexive, and I believe we have that
    -- the total space is contractible.  So this should be enought to show that
    -- the relation is equality.

    R-is-== : (i : Idx M) (x y : Ob X i) → (R i x y) ≃ (x == y)
    R-is-== i x y = fundamental-thm (Ob X i) (λ a → R i x a) x (refl i x) (base-fibrant is-fib i (η M i) (cst x)) y


  -- fundamental-thm : ∀ {i} (A : Type i) (P : A → Type i)
  --   → (a₀ : A) (r : P a₀) (is-c : is-contr (Σ A P))
  --   → (a₁ : A) → P a₁ ≃ (a₀ == a₁)
  -- fundamental-thm A P a₀ r is-c a₁ = equiv to from to-from from-to 



  -- record is-fibrant {M : 𝕄} (X : OpetopicType M) : Set where
  --   coinductive
  --   field

  --     base-fibrant : unique-action M (Ob X) (Ob (Hom X))
  --     hom-fibrant : is-fibrant (Hom X)
    
  -- unique-action : (M : 𝕄) (A : Idx M → Set)
  --   → (W : Idx (Slice (Pb M A)) → Set)
  --   → Set
  -- unique-action M A W = (f : Idx M) (σ : Cns M f)
  --   → (ν : (p : Pos M σ) → A (Typ M σ p))
  --   → is-contr (Σ (A f) (λ a → W ((f , a) , σ , ν)))


