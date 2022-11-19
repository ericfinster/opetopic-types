--
--  Monads.agda - an inductive presentation of monads
--

open import Core.Prelude

module Experimental.Monads where

  data 𝕄 : Type₁ 

  Idx : 𝕄 → Type
  Cns : (M : 𝕄) → Idx M → Type 
  Pos : (M : 𝕄) (i : Idx M) → Cns M i → Type
  Typ : (M : 𝕄) (i : Idx M) (c : Cns M i)
    → Pos M i c → Idx M 

  data 𝕄 where
    𝕋 : 𝕄
    _/_ : (M : 𝕄) (X : Idx M → Type) → 𝕄 

  Idx 𝕋 = 𝟙 ℓ-zero
  Idx (M / X) = Σ[ i ∈ Idx M ]
                Σ[ c ∈ Cns M i ]
                Σ[ ν ∈ ((p : Pos M i c) → X (Typ M i c p)) ]
                X i

  Cns = {!!} 
  Pos = {!!}
  Typ = {!!} 
