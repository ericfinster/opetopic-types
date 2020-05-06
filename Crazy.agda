{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import Pb

module Crazy where

  postulate

    𝕆 : 𝕄 → Set

    Ob : (M : 𝕄) (X : 𝕆 M) → Frm M → Set
    Hom : (M : 𝕄) (X : 𝕆 M) → 𝕆 (Slice (Pb M (Ob M X))) 
