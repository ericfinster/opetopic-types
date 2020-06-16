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

  record GMap (X Y : GType) : Set where
    coinductive
    field
      f-ob : GOb X → GOb Y
      f-hom : (x y : GOb X)
        → GMap (GHom X x y) (GHom Y (f-ob x) (f-ob y))

  record GEquiv' (X Y : GType) (e : GOb X ≃ GOb Y) : Set where
    coinductive
    field
      HomEqv : (x y : GOb X)
        → (GOb (GHom X x y)) ≃ (GOb (GHom Y (–> e x) (–> e y)))
      AndThen : (x y : GOb X)
        → GEquiv' (GHom X x y) (GHom Y (–> e x) (–> e y)) (HomEqv x y)

  record GEquiv (X Y : GType)  : Set where
    coinductive
    field
      ObEqv : GOb X ≃ GOb Y
      HomEqv : (x y : GOb X)
        → GEquiv (GHom X x y) (GHom Y (–> ObEqv x) (–> ObEqv y))


  TypeToGType : (X : Set) → GType
  GOb (TypeToGType X) = X
  GHom (TypeToGType X) x y = TypeToGType (x == y)

  OpetopicToGlobular : (M : 𝕄) (X : OpetopicType M) → Idx M → GType
  GOb (OpetopicToGlobular M X i) = Ob X i
  GHom (OpetopicToGlobular M X i) x y =
    OpetopicToGlobular (Slice (Pb M (Ob X))) (Hom X)
                       ((i , y) , (η M i , λ _ → x))

  module _ (M : 𝕄) (X : OpetopicType M) (is-fib : is-fibrant X) where

    R : (i : Idx M) (x y : Ob X i) → Set
    R i x y = Ob (Hom X) ((i , y) , (η M i , λ _ → x)) 

    refl : (i : Idx M) (x : Ob X i) → R i x x
    refl i x = fst (contr-center (base-fibrant (hom-fibrant is-fib) ((i , x) , (η M i , cst x)) (lf (i , x)) ⊥-elim))

    R-is-== : (i : Idx M) (x y : Ob X i) → (R i x y) ≃ (x == y)
    R-is-== i x y = fundamental-thm (Ob X i) (λ a → R i x a) x (refl i x) (base-fibrant is-fib i (η M i) (cst x)) y

  claim : (M : 𝕄) (i : Idx M)
    → (X : OpetopicType M) (A : Set)
    → (eqv : Ob X i ≃ A)
    → (is-fib : is-fibrant X) 
    → GEquiv (OpetopicToGlobular M X i) (TypeToGType A) 
  GEquiv.ObEqv (claim M i X A eqv is-fib) = eqv
  GEquiv.HomEqv (claim M i X A eqv is-fib) x y =
    {!claim (Slice (Pb M (Ob X))) ((i , y) , η M i , (λ _ → x)) (Hom X) (x == y) ? (hom-fibrant is-fib)!}

  -- I see.  So compose this with the fact that an equivalence induces
  -- an equivalence on path spaces.  Something like that should work
