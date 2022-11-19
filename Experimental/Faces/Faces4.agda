--
--  Faces.agda - Faces of an opetopic type
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.OpetopicType
open import Core.OpetopicMap

module Lib.Faces4 where

  Stem : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → 𝕆Type n ℓ

  StemLfFrm : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f) (p : Pos P s)
    → Frm (Stem X P f s)

  StemNdFrm : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (U : Frm (X , P) → Type ℓ)
    → (f : Frm X) (s : Src P f) (t : P f)
    → (ρ : Pd U (f , s , t)) (p : Pos U ρ)
    → Frm (Stem X P f s)

  StemTotalFrm : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f) 
    → Frm (Stem X P f s)

  data StemCell {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
      (U : Frm (X , P) → Type ℓ)
      (f : Frm X) (s : Src P f) (t : P f)
      (ρ : Pd U (f , s , t)) : Frm (Stem X P f s) → Type ℓ 

  StemTgtSrc : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (U : Frm (X , P) → Type ℓ)
    → (f : Frm X) (s : Src P f) (t : P f)
    → (ρ : Pd U (f , s , t)) 
    → Src (StemCell X P U f s t ρ) (StemTotalFrm X P f s)




  Stem {zero} X P f s = tt*
  Stem {suc n} (X , P) U (f , s , t) ρ =
    Stem X P f s , StemCell X P U f s t ρ

  data StemCell {n} {ℓ} X P U f s t ρ where

    lf-cell : (p : Pos P s) → StemCell X P U f s t ρ (StemLfFrm X P f s p)

    nd-cell : (p : PdPos U ρ) → StemCell X P U f s t ρ (StemNdFrm X P U f s t ρ p)

  StemNdFrm X P U f ._ ._ (nd src tgt flr brs) nd-here = StemTotalFrm X P f (canopy U {s = src} brs)
  StemNdFrm X P U f ._ ._ (nd src tgt flr brs) (nd-there p q) = {!Stem!}

  StemLfFrm {zero} X P f s p = tt*
  StemLfFrm {suc n} (X , P) U (f , ._ , .tgt) (nd src tgt flr brs) nd-here = {!!} 
  StemLfFrm {suc n} (X , P) U (f , ._ , .tgt) (nd src tgt flr brs) (nd-there p q) = {!!} 


  StemTotalFrm {zero} X P f s = tt*
  StemTotalFrm {suc n} (X , P) U (f , s , t) ρ = {!!} 

  StemTgtSrc = {!!}                                
