{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import Pb

module Experiments where

  record OpetopicType (M : 𝕄) : Set₁ where
    coinductive
    field
    
      Ob : Frm M → Set
      Hom : OpetopicType (Slice (Pb M Ob))

  open OpetopicType

  postulate

    -- So I think this equivalence should be semantic, in the sense
    -- that it can be implemented and need not be axiomatic.
    intchg : (M : 𝕄) (E : Frm M → Set) (F : Frm M → Set)
      → Pb (Slice (Pb M F)) (E ∘ fst ∘ fst) == Slice (Pb (Pb M E) (F ∘ fst)) 
  
    -- That we can obtain equalities of monads from isomorphisms is
    -- a consequence of univalence and I don't think is in any way
    -- affected by the extra definitional equalities satisfied by
    -- the monad signatures.

  {-# TERMINATING #-}
  Wk : (M : 𝕄) (X : OpetopicType M)
    → (E : Frm M → Set)
    → OpetopicType (Pb M E)
  Ob (Wk M X E) = Ob X ∘ fst
  Hom (Wk M X E) = transport OpetopicType (intchg M E (Ob X))
    (Wk (Slice (Pb M (Ob X))) (Hom X) (E ∘ fst ∘ fst))

  -- So, how might this work?


    -- Dependent sum of dependent monads
    ΣM : (M : 𝕄) (M↓ : 𝕄↓ M) → 𝕄

    Frm-ΣM : (M : 𝕄) (M↓ : 𝕄↓ M)
      → Frm (ΣM M M↓) ↦ Σ (Frm M) (Frm↓ M↓)
    {-# REWRITE Frm-ΣM #-}

  -- Ah! Bingo.  This version doesn't require any kind of transporting
  -- to define.  But does it make sense? 
  record OpetopicType↓ (M : 𝕄) (M↓ : 𝕄↓ M) (X : OpetopicType M) : Set₁ where
    coinductive
    field

      Ob↓ : (f : Frm M) → Ob X f → Frm↓ M↓ f → Set
      Hom↓ : OpetopicType↓ (Slice (Pb M (Ob X))) (Slice↓ (Pb↓ M↓ (Ob X) Ob↓)) (Hom X)

  open OpetopicType↓

  -- Oh!  But maybe the target monad is just M? 
  ΣO : (M : 𝕄) (M↓ : 𝕄↓ M) (X : OpetopicType M) (Y : OpetopicType↓ M M↓ X) → OpetopicType (ΣM M M↓)
  Ob (ΣO M M↓ X Y) (f , f↓) = Σ (Ob X f) (λ x → Ob↓ Y f x f↓)
  Hom (ΣO M M↓ X Y) = {!ΣO (Slice (Pb M (Ob X))) (Slice↓ (Pb↓ M↓ (Ob X) (Ob↓ Y))) (Hom X) (Hom↓ Y)!}

  ΣO' : (M : 𝕄) (M↓ : 𝕄↓ M) (X : OpetopicType M) (Y : OpetopicType↓ M M↓ X) → OpetopicType M
  Ob (ΣO' M M↓ X Y) f = Σ (Frm↓ M↓ f) (λ f↓ → Σ (Ob X f) (λ x → Ob↓ Y f x f↓ ))
  Hom (ΣO' M M↓ X Y) = {!ΣO' (Slice (Pb M (Ob X))) (Slice↓ (Pb↓ M↓ (Ob X) (Ob↓ Y))) (Hom X) (Hom↓ Y)!}

-- So we would need to transport by the following:
-- Goal: OpetopicType (Slice (Pb (ΣM M M↓) (Ob (ΣO M M↓ X Y))))
-- Have: OpetopicType (ΣM (Slice (Pb M (Ob X))) (Slice↓ (Pb↓ M↓ (Ob X) (Ob↓ Y))))

  -- 
  -- So there you go.  The notion of dependent opetopic type.
  -- Can we write the sum and product?
  --
  
  -- record OpetopicType↓ (M : 𝕄) (X : OpetopicType M) : Set₁ where
  --   coinductive
  --   field

  --     Ob↓ : Σ (Frm M) (Ob X) → Set 
  --     Hom↓ : OpetopicType↓ (Pb (Slice (Pb M (Ob X))) (Ob↓ ∘ fst))
  --                          (Wk (Slice (Pb M (Ob X))) (Hom X) (Ob↓ ∘ fst))

  -- open OpetopicType↓ 
  
  -- ΣO : (M : 𝕄) (X : OpetopicType M) (Y : OpetopicType↓ M X) → OpetopicType M
  -- Ob (ΣO M X Y) f = Σ (Ob X f) (λ x → Ob↓ Y (f , x))
  -- Hom (ΣO M X Y) = {!ΣO (Pb (Slice (Pb M (Ob X))) (Ob↓ Y ∘ fst)) (Wk (Slice (Pb M (Ob X))) (Hom X) (Ob↓ Y ∘ fst)) (Hom↓ Y)!}

  -- -- Mmmm.  Indeed.  So we'll have to use a similar transport trick,
  -- -- and then an associative iso on iterated pullbacks.

  -- ΠO : (M : 𝕄) (X : OpetopicType M) (Y : OpetopicType↓ M X) → OpetopicType M
  -- Ob (ΠO M X Y) f = Π (Ob X f) (λ x → Ob↓ Y (f , x))
  -- Hom (ΠO M X Y) = {!ΠO (Pb (Slice (Pb M (Ob X))) (Ob↓ Y ∘ fst)) (Wk (Slice (Pb M (Ob X))) (Hom X) (Ob↓ Y ∘ fst)) (Hom↓ Y)!}

  -- I don't officially see why this is problematic, but with respect
  -- to the issues you wanted to think about: monad augmentations and
  -- so on, it does not seem immediately relevant.

  -- Also, what about Π?

  -- Yeah, I'm a bit confused.  Because Π is supposed to quantify over
  -- frames as well, but that doesn't seem to make sense here.  So I
  -- feel that something is missing.  And I feel it has to do with
  -- this notion of dependent monad somehow.  But I don't yet see what
  -- to do ....

  -- Hmmm.  Not super happy about this.  Seem to be getting stuck.
  -- What can we do?
