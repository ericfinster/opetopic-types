{-# OPTIONS --rewriting #-}

open import Cubical.Core.Everything 

module Core.Prelude where

  infix 10 _↦_
  postulate  
    _↦_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ

  {-# BUILTIN REWRITE _↦_ #-}

  -- Inductive identity types.
  data Ident {ℓ} (A : Type ℓ) (a : A) : A → Type ℓ where
    idp : Ident A a a 
