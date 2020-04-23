{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType

module Experiments where

  open OpetopicType.OpetopicType

  -- exactly. we need a kind of projection/weakening operator...

  wk : (M : 𝕄) (F : Filler M)
    → (F↑ : {f : Frm M} (σ : Tree M f) (τ : Cell M f) → F σ τ → Set)
    → (X : OpetopicType (Slice M F))
    → OpetopicType (Slice M (λ σ τ → Σ (F σ τ) (F↑ σ τ)))
  OpetopicType.Flr (wk M F F↑ X) σ τ = {!!} -- Flr X {!σ!} {!τ!}
  OpetopicType.Hom (wk M F F↑ X) = {!!}

  -- record OpetopicTypeOver (M : 𝕄) (X : OpetopicType M) : Set₁ where
  --   coinductive
  --   field

  --     F↑ : {f : Frm M} (σ : Tree M f) (τ : Cell M f) → F X σ τ → Set
  --     H↑ : OpetopicTypeOver (Slice M (λ σ τ → Σ (F X σ τ) (F↑ σ τ))) {!H X!}
      

