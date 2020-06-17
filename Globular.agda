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

  record _≃g_ (X Y : GType)  : Set where
    coinductive
    field
      ObEqv : GOb X ≃ GOb Y
      HomEqv : (x y : GOb X)
        → (GHom X x y) ≃g (GHom Y (–> ObEqv x) (–> ObEqv y))

  open _≃g_ public

  _∘g_ : {X Y Z : GType} (f : Y ≃g Z) (g : X ≃g Y) → X ≃g Z
  ObEqv (f ∘g g) = ObEqv f ∘e ObEqv g
  HomEqv (f ∘g g) x y = HomEqv f (–> (ObEqv g) x) (–> (ObEqv g) y) ∘g HomEqv g x y

  IdG : (X : Set) → GType
  GOb (IdG X) = X
  GHom (IdG X) x y = IdG (x == y)

  equiv-to-g-equiv : (X Y : Set) (e : X ≃ Y) → IdG X ≃g IdG Y
  ObEqv (equiv-to-g-equiv X Y e) = e
  HomEqv (equiv-to-g-equiv X Y e) x y =
    equiv-to-g-equiv (x == y) (–> e x == –> e y) (ap-equiv e x y)

  OpToGlob : (M : 𝕄) (X : OpetopicType M) → Idx M → GType
  GOb (OpToGlob M X i) = Ob X i
  GHom (OpToGlob M X i) x y =
    OpToGlob (Slice (Pb M (Ob X))) (Hom X)
                       ((i , y) , (η M i , λ _ → x))

  module _ (M : 𝕄) (X : OpetopicType M) (is-fib : is-fibrant X) where

    R : (i : Idx M) (x y : Ob X i) → Set
    R i x y = Ob (Hom X) ((i , y) , (η M i , λ _ → x)) 

    refl : (i : Idx M) (x : Ob X i) → R i x x
    refl i x = fst (contr-center (base-fibrant (hom-fibrant is-fib) ((i , x) , (η M i , cst x)) (lf (i , x)) ⊥-elim))

    R-is-== : (i : Idx M) (x y : Ob X i) → (R i x y) ≃ (x == y)
    R-is-== i x y = fundamental-thm (Ob X i) (λ a → R i x a) x (refl i x) (base-fibrant is-fib i (η M i) (cst x)) y

  {-# TERMINATING #-}
  fibrant-is-eq : (M : 𝕄) (i : Idx M)
    → (X : OpetopicType M) (A : Set)
    → (eqv : Ob X i ≃ A)
    → (is-fib : is-fibrant X) 
    → OpToGlob M X i ≃g IdG A 
  ObEqv (fibrant-is-eq M i X A eqv is-fib) = eqv
  HomEqv (fibrant-is-eq M i X A eqv is-fib) x y =
    HomEqv (equiv-to-g-equiv (Ob X i) A eqv) x y ∘g
      (fibrant-is-eq (Slice (Pb M (Ob X))) ((i , y) , η M i , (λ _ → x))
             (Hom X) (x == y) (R-is-== M X is-fib i x y) (hom-fibrant is-fib))

  corollary : (M : 𝕄) (i : Idx M) (X : OpetopicType M)
    → (is-fib : is-fibrant X)
    → OpToGlob M X i ≃g IdG (Ob X i)
  corollary M i X is-fib =
    fibrant-is-eq M i X (Ob X i) (ide (Ob X i)) is-fib 
