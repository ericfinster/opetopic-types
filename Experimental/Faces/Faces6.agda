--
--  Faces.agda - Faces of an opetopic type
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.OpetopicType
open import Core.OpetopicMap

module Lib.Faces6 where

  Stem : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → 𝕆Type n ℓ

  StemSrcFrm : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f) (p : Pos P s)
    → Frm (Stem X P f s)

  StemTgtFrm : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f) 
    → Frm (Stem X P f s)

  StemNdFrm : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (U : Frm (X , P) → Type ℓ)
    → (f : Frm X) (s : Src P f) (t : P f)
    → (ρ : Pd U (f , s , t)) (p : Pos U ρ)
    → Frm (Stem X P f s)

  data StemCell {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
      (U : Frm (X , P) → Type ℓ)
      (f : Frm X) (s : Src P f) (t : P f)
      (ρ : Pd U (f , s , t)) : Frm (Stem X P f s) → Type ℓ 

  Stem {zero} X P f s = tt*
  Stem {suc n} (X , P) U (f , s , t) ρ =
    Stem X P f s , StemCell X P U f s t ρ

  data StemCell {n} {ℓ} X P U f s t ρ where

    lf-cell : (p : Pos P s) → StemCell X P U f s t ρ (StemSrcFrm X P f s p)

    nd-cell : (p : PdPos U ρ) → StemCell X P U f s t ρ (StemNdFrm X P U f s t ρ p)

  StemNdCnpy : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (U : Frm (X , P) → Type ℓ)
    → (f : Frm X) (s : Src P f) (t : P f)
    → (ρ : Pd U (f , s , t)) (p : Pos U ρ)
    → Src (StemCell X P U f s t ρ) (StemNdFrm X P U f s t ρ p)

  StemSrcFrm {zero} X P f s p = tt*
  StemSrcFrm {suc n} (X , P) U (f , s , t) ρ p =
    StemNdFrm X P U f s t ρ p , StemNdCnpy X P U f s t ρ p , nd-cell p

  StemNdFrm X P U f ._ ._ (nd src tgt flr brs) nd-here = StemTgtFrm X P f (canopy U {s = src} brs)  -- So here it's the maximal frame ... 
  StemNdFrm X P U f ._ ._ (nd src tgt flr brs) (nd-there p q) = {!!}

  StemNdCnpy X P U f ._ ._ (nd src tgt flr brs) nd-here = {!!}  -- ... but this is *not* the canonical tree.
  StemNdCnpy X P U f ._ ._ (nd src tgt flr brs) (nd-there p q) = {!!}

  --
  --  Problem is to compute the *target* frame
  --

  -- Nice! By computing the target frame by induction on the pasting digram, we can
  -- actually select the source face at the position as the correct answer in the leaf
  -- case and get what looks like the right answer.

  StemTgtFrm {zero} X P f s = tt*
  
  StemTgtFrm {suc n} (X , P) U (frm , ._ , .tgt) (lf tgt) =
    StemSrcFrm X P frm (η P tgt) (η-pos P tgt) ,
    η (StemCell X P U frm (η P tgt) tgt (lf tgt)) (lf-cell (η-pos P tgt)) ,
    lf-cell (η-pos P tgt)
    
  StemTgtFrm {suc n} (X , P) U (frm , ._ , .tgt) (nd src tgt flr brs) =
    StemTgtFrm X P frm (canopy U {s = src} brs) ,
    {!!} ,
    nd-cell nd-here
  

  -- Okay, nice, this is starting to look good!  This is the first
  -- time you got so far in the position version.  At this point, it
  -- would see we need our bind decomposition guys.

  -- Or, I guess, you're kind of doing it by hand in the version.

  -- So in the latest, the idea would be to bind to the node canopy a
  -- recursive call.  Which means we need to figure out how to finish
  -- the node canopy.
