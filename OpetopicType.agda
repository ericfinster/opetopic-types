{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import Pb

module OpetopicType where

  --
  --  The definition of opetopic type
  --

  record OpetopicType (M : 𝕄) : Set₁ where
    coinductive
    field
    
      Ob : Frm M → Set
      Hom : OpetopicType (Slice (Pb M Ob))

  open OpetopicType public

  record OpetopicTerm (M : 𝕄) (X : OpetopicType M) (A : Set) (ϕ : A → Frm M) : Set where
    coinductive
    field

      ob : (a : A) → Ob X (ϕ a)
      hom : OpetopicTerm (Slice (Pb M (Ob X))) (Hom X) (Σ A (λ a → Tree M (ϕ a))) (λ { (a , σ) → (ϕ a , ob a) , (σ , (λ p → {!!})) })

  -- Hmmm.  I guess this isn't quite right.  But I guess there's
  -- something to think about here.  What if, instead of *every*
  -- frame, you pick a guy over *some* frame.


  -- action : (M : 𝕄) (A : Frm M → Set) → Set
  -- action M A = (f : Frm M) (σ : Tree M f)
  --   → (ν : (p : Pos M σ) → A (Typ M σ p))
  --   → A f 

  -- unique-action : (M : 𝕄) (A : Frm M → Set)
  --   → (W : Frm (Slice (ΣM M (Ext M A))) → Set)
  --   → Set
  -- unique-action M A W = (f : Frm M) (σ : Tree M f)
  --   → (ν : (p : Pos M σ) → A (Typ M σ p))
  --   → is-contr (Σ (A f) (λ a → W ((f , a) , σ , ν)))
    
  -- record is-fibrant {M : 𝕄} (X : OpetopicType M) : Set where
  --   coinductive
  --   field

  --     base-fibrant : unique-action M (Ob X) (Ob (Hom X))
  --     hom-fibrant : is-fibrant (Hom X)

  -- open is-fibrant public

  -- -- The terminal opetopic type.
  -- Terminal : (M : 𝕄) → OpetopicType M
  -- Ob (Terminal M) = cst ⊤
  -- Hom (Terminal M) = Terminal (Slice (ΣM M (Ext M (cst ⊤))))
  
  -- Trees : (M : 𝕄) → OpetopicType M
  -- Ob (Trees M) = Tree M
  -- Hom (Trees M) = Trees (Slice (ΣM M (Ext M (Tree M))))

  -- -- No, I think it's neither one of these.  There are too many trees
  -- -- to be equivalent to the path type.  And the terminal guy
  -- -- identities everything.

  -- -- Can you use the trees to get the right answer, though?  Somehow
  -- -- you want to restrict to "trees of length 1", i.e. those in the
  -- -- image (hmmm, why not just say this?) of η.  Not sure exactly what
  -- -- this means.

  -- -- Anyway, I think I like the setup, but there's still something to
  -- -- understand in order to get this right.

  -- -- Or maybe the are somehow trees equipped with a null homotopy.
  -- -- I guess this is somehow the same as saying they are equal or
  -- -- in the image of η?  Or something?

  -- --
  -- -- Here's Thorsten's syntax for a dependent coinductive
  -- -- definition.  I agree totally that this is somehow what
  -- -- the definition is suppsosed to look like.
  -- --
  
  -- -- record OpetopicType : 𝕄 → Set₁ where
  -- --   coinductive
  -- --   destructor
    
  -- --     Ob : (M : 𝕄) → Frm M → Set
  -- --     Hom : (M : 𝕄) → OpetopicType (Slice (ΣM M (Ext M (Ob M))))

  -- -- Yeah.  It's true that this is better.
