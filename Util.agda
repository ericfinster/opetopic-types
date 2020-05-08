{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Universe

module Util where

  --
  --  Currying of strict sigma
  --
  
  curryₛ : {A : 𝕌} {B : El A → 𝕌} {C : Set}
    → (D : El (Σₛ A B) → C)
    → (a : El A) → El (B a) → C
  curryₛ {A} {B} {C} D a b = D (prₛ A B a b) 

  uncurryₛ : {A : 𝕌} {B : El A → 𝕌} {C : Set}
    → (D : (a : El A) → El (B a) → C)
    → El (Σₛ A B) → C
  uncurryₛ {A} {B} {C} D s = D (fstₛ A B s) (sndₛ A B s) 

  --
  --  Recursors
  --

  ⊔ₛ-rec : (A B : 𝕌) {C : Set}
    → (inl* : El A → C) (inr* : El B → C)
    → El (A ⊔ₛ B) → C
  ⊔ₛ-rec A B {C} inl* inr* =
    ⊔ₛ-elim A B (cst C) inl* inr*


