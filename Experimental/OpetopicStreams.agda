--
--  Opetopes.agda - Underlying shapes for opetopic types
--

open import Cubical.Foundations.Everything 
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum 

open import Core.Prelude

module Experimental.OpetopicStreams where

  --
  --  Streams of polynomials ...
  --

  record PolyStream (I : Type) : Type₁ where
    coinductive
    field
      C : I → Type
      P : (i : I) (c : C i) → Type
      T : (i : I) (c : C i) (p : P i c) → I

      N : PolyStream (Σ I C) 

