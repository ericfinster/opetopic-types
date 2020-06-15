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

  module _ (M : 𝕄) (X : OpetopicType M) (is-fib : is-fibrant X) where

    R : (i : Idx M) (x y : Ob X i) → Set
    R i x y = Ob (Hom X) ((i , y) , (η M i , λ _ → x)) 

    refl : (i : Idx M) (x : Ob X i) → R i x x
    refl i x = fst (contr-center (base-fibrant (hom-fibrant is-fib) ((i , x) , (η M i , cst x)) (lf (i , x)) ⊥-elim))

    R-is-== : (i : Idx M) (x y : Ob X i) → (R i x y) ≃ (x == y)
    R-is-== i x y = fundamental-thm (Ob X i) (λ a → R i x a) x (refl i x) (base-fibrant is-fib i (η M i) (cst x)) y

