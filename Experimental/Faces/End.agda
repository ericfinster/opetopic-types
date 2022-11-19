--
--  Faces.agda - Faces of an opetopic type
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.OpetopicType
open import Core.OpetopicMap
open import Core.Universe

open import Lib.Terminal
open import Lib.Opetopes
open import Lib.Structures

module Experimental.Faces.End where

  postulate

    X : 𝕆Type∞ {ℓ = ℓ-zero} tt*

    B : {n : ℕ} → 𝒪 n → 𝕆Type∞ {ℓ = ℓ-zero} tt* 
    D : {n : ℕ} → 𝒪 n → 𝕆Type∞ {ℓ = ℓ-zero} tt* 
  
    ι : {n : ℕ} (𝑜 : 𝒪 n) → Map tt* (B 𝑜) (D 𝑜) 

  -- So, one idea is that you see the stem as some kind of
  -- fixed opetopic type for each n and then the boundary
  -- and the disk as two distinct extensions with inclusion
  -- maps ...


  End : (n : ℕ) → 𝕆Type n ℓ-zero
  Decode : {n : ℕ} (f : Frm (End n)) → Map tt* (B (Shape f)) X 

  End zero = tt*
  End (suc n) = End n , λ f →
    Σ[ σ ∈ Map tt* (D (Shape f)) X ]
    Decode f ≡ (σ ⊙∞ ι (Shape f))

  -- Yeah, interesting.
  Decode {zero} tt* = {!!} -- Need a map to start ...
  Decode {suc n} (f , s , t) = {!!}

    where ih : Map tt* (B (Shape f)) X
          ih = Decode f 

  -- And so what do we get from the induction hypothesis?
  -- Right.  We get this map depending on the shape of f...

  -- So here it seems like you are keeping a lot of data.  Maybe
  -- that's okay after eliminating the identity.  But perhaps
  -- a better strategy would be to fix the stem first for
  -- every opetope and then have some kind of extensions.

  -- Dunno.

  -- In any case, we now seem to need an operation on B or D (or both)
  -- which explains how it behaves under extension of the shape.

  -- And this should essentially express the idea that the B's are the
  -- *colimit* of the D's.  The idea of the "stems" is to say that
  -- this colimit in some sense stabilizes and only depends on the
  -- stem and the interaction of the first two codimensions.

  -- What would be a reasonable way to express this colimit property?

  -- Does one have to quantify over all maps?  This would seem to have
  -- some annoying issues with the dependence on the universe level.

  -- So you could suppose that you have inclusion maps for local
  -- faces.  Then you could define a type of "heterogenous" trees
  -- which took values in the various individually defined pieces.
  -- The idea would be that this type came together with a map
  -- including it into the next stage.  And this idea would be to
  -- say that this map is somehow an isomorphism.....
