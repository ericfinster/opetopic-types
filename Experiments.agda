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

  {-# TERMINATING #-}
  Wk : (M : 𝕄) (X : OpetopicType M)
    → (E : Frm M → Set)
    → OpetopicType (Pb M E)
  Ob (Wk M X E) = Ob X ∘ fst
  Hom (Wk M X E) = transport OpetopicType (intchg M E (Ob X))
    (Wk (Slice (Pb M (Ob X))) (Hom X) (E ∘ fst ∘ fst))

  -- So, how might this work?

  postulate

    𝕄↓ : (M : 𝕄) → Set

    Frm↓ : {M : 𝕄} (M↓ : 𝕄↓ M) → Frm M → Set 
    Tree↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Frm M} (f↓ : Frm↓ M↓ f)
      → Tree M f → Set 

    Typ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Frm M} (f↓ : Frm↓ M↓ f)
      → {σ : Tree M f} (σ↓ : Tree↓ M↓ f↓ σ)
      → (p : Pos M σ) → Frm↓ M↓ (Typ M σ p)

    -- Dependent sum of dependent monads
    ΣM : (M : 𝕄) (M↓ : 𝕄↓ M) → 𝕄

  -- 
  -- So there you go.  The notion of dependent opetopic type.
  -- Can we write the sum and product?
  --
  
  record OpetopicType↓ (M : 𝕄) (X : OpetopicType M) : Set₁ where
    coinductive
    field

      Ob↓ : Σ (Frm M) (Ob X) → Set 
      Hom↓ : OpetopicType↓ (Pb (Slice (Pb M (Ob X))) (Ob↓ ∘ fst))
                           (Wk (Slice (Pb M (Ob X))) (Hom X) (Ob↓ ∘ fst))

  open OpetopicType↓ 
  
  ΣO : (M : 𝕄) (X : OpetopicType M) (Y : OpetopicType↓ M X) → OpetopicType M
  Ob (ΣO M X Y) f = Σ (Ob X f) (λ x → Ob↓ Y (f , x))
  Hom (ΣO M X Y) = {!ΣO (Pb (Slice (Pb M (Ob X))) (Ob↓ Y ∘ fst)) (Wk (Slice (Pb M (Ob X))) (Hom X) (Ob↓ Y ∘ fst)) (Hom↓ Y)!}

  -- Mmmm.  Indeed.  So we'll have to use a similar transport trick,
  -- and then an associative iso on iterated pullbacks.

  ΠO : (M : 𝕄) (X : OpetopicType M) (Y : OpetopicType↓ M X) → OpetopicType M
  Ob (ΠO M X Y) f = Π (Ob X f) (λ x → Ob↓ Y (f , x))
  Hom (ΠO M X Y) = {!ΠO (Pb (Slice (Pb M (Ob X))) (Ob↓ Y ∘ fst)) (Wk (Slice (Pb M (Ob X))) (Hom X) (Ob↓ Y ∘ fst)) (Hom↓ Y)!}

  -- I don't officially see why this is problematic, but with respect
  -- to the issues you wanted to think about: monad augmentations and
  -- so on, it does not seem immediately relevant.

  -- Also, what about Π?

  -- Yeah, I'm a bit confused.  Because Π is supposed to quantify over
  -- frames as well, but that doesn't seem to make sense here.  So I feel
  -- that something is missing.  And I feel it has to do with this notion
  -- of dependent monad somehow.  But I don't yet see what to do ....

  -- Hmmm.  Not super happy about this.  Seem to be getting stuck.  What
  -- can we do? 
