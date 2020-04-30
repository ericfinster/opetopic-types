{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import Pb
-- open import FundamentalThm

module OpetopicType where

  --
  --  The definition of opetopic type
  --

  record OpetopicType (M : 𝕄) : Set₁ where
    coinductive
    field
    
      Ob : Frm M → Set
      Hom : OpetopicType (Slice (Pb M Ob))

  open OpetopicType


  -- record OpetopicType (M : 𝕄) : Set₁ where
  --   coinductive
  --   field

  --     Flr : Filler M
  --     Hom : OpetopicType (Slice M Flr)

  -- -- Now, some auxillary definitions

  -- open OpetopicType public

  -- has-unique-comps : (M : 𝕄) (F : Filler M) → Set
  -- has-unique-comps M F = (f : Frm M) (σ : Tree M f)
  --   → is-contr (Σ (Cell M f) (λ τ → F σ τ))
    
  -- record is-fibrant {M : 𝕄} (X : OpetopicType M) : Set where
  --   coinductive
  --   field

  --     base-fibrant : has-unique-comps M (Flr X)
  --     hom-fibrant : is-fibrant (Hom X)

  -- open is-fibrant public

  -- comp-fun : (M : 𝕄) (F : Filler M) (uc : has-unique-comps M F)
  --   → {f : Frm M} → Tree M f → Cell M f
  -- comp-fun M F uc {f} σ = fst (fst (has-level-apply (uc f σ)))

  -- filler-fun : (M : 𝕄) (F : Filler M) (uc : has-unique-comps M F)
  --   → {f : Frm M} (σ : Tree M f)
  --   → F σ (comp-fun M F uc σ)
  -- filler-fun M F uc {f} σ = snd (fst (has-level-apply (uc f σ)))

  -- fillers-are-pths : (M : 𝕄) (F : Filler M) (uc : has-unique-comps M F)
  --   → {f : Frm M} (σ : Tree M f) (τ : Cell M f)
  --   → F σ τ ≃ (comp-fun M F uc σ == τ)
  -- fillers-are-pths M F uc {f} σ τ =
  --   fundamental-thm (Cell M f) (F σ) (comp-fun M F uc σ)
  --     (filler-fun M F uc σ) (uc f σ) τ
