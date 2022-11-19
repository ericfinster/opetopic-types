{-# OPTIONS --cubical #-}

open import Core.Prelude hiding (Σ-syntax)
open import Cubical.Foundations.Everything

module Native.Scratch where

  data _==_ {A : Type} : A → A → Type where
    idp : (a : A) → a == a 


  claim : (A : Type) (a : A) → isContr (Σ[ b ∈ A ] a == b)
  claim A a = (a , idp a) , unique 

    where unique : (p : Σ[ b ∈ A ] (a == b)) → (a , idp a) ≡ p
          unique (fst₁ , idp .fst₁) = refl
