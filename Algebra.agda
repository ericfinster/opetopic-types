{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import Pb 

module Algebra where

  postulate

    𝔸 : 𝕄 → Set
    
    Carrier : {M : 𝕄} (A : 𝔸 M) → Frm M → Set 
    Relations : {M : 𝕄} (A : 𝔸 M) → 𝔸 (Slice (Pb M (Carrier A))) 

  -- So, given an algebra, there should be a monad over M
  -- corresponding to the Baez-Dolan slice construction. 
