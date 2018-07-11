{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT
open import PolyMonads

module EtaTest where

  module _ (M : Mnd) where

    -- Place calculation
    slc-from-rec : (i : Idx (slc M))
      → ηρ (slc M) i == ρ (slc M) i (η (slc M) i)
    slc-from-rec i = idp

