--
--  Scratch.agda - Random things I'm working on 
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat 
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open import Core.Prelude
open import Core.Everything

module Experimental.Scratch where

  data Tr (A : Type) : ℕ → Type where

    obj : A → Tr A 0

    lf : {n : ℕ}
      → Tr A (suc n)
    
    nd : {n : ℕ} → A
      → Tr (Tr A (suc n)) n 
      → Tr A (suc n) 


