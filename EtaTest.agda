{-# OPTIONS --without-K --rewriting --verbose=tc.meta.eta:40 --verbose=tc.meta.assign.proj:45 --verbose=tc.conv.elim:50 --verbose=tc.proj.like:70 #-}

open import HoTT

module EtaTest where

  module _ (X : Type₀) (P : X → Type₀) where

    eta : (p : Σ X P) → (fst p , snd p) == p
    eta p = {!!}

    -- silly : ⊤ → X
    -- silly unit = x

    -- -- And how does this work?
    -- another : (u : ⊤) → u == unit
    -- another u = idp

    -- -- Uh, yeah.  So you have to understand how this works.
    -- η-test : (u : ⊤) → x == silly u
    -- η-test u = idp
