--
--  Faces.agda - Faces of an opetopic type
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.OpetopicType
open import Core.OpetopicMap

module Experimental.Faces.Faces where

  Bdry : ∀ {n ℓ} (X : 𝕆Type n ℓ) (f : Frm X)
    → 𝕆Type n ℓ 

  Stem : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → 𝕆Type n ℓ

  SrcIncl : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f) (p : Pos P s)
    → Bdry X (Typ P s p) ⇒ Stem X P f s

  TgtIncl : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → Bdry X f ⇒ Stem X P f s

  BdryFrm : ∀ {n ℓ} (X : 𝕆Type n ℓ) (f : Frm X) → Frm (Bdry X f)

  data BdryCell {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    (f : Frm X) (s : Src P f) : Frm (Stem X P f s) → Type ℓ 

  BdrySrc : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → Src (BdryCell X P f s) (Frm⇒ (TgtIncl X P f s) (BdryFrm X f))

  NdIncl : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (U : Frm (X , P) → Type ℓ)
    → (f : Frm X) (s : Src P f) (t : P f)
    → (ρ : Pd U (f , s , t)) (p : PdPos U ρ)
    → Bdry X (fst (Typ U ρ p)) ⇒ Stem X P f s


  data BdryCell {n} {ℓ} X P f s where

    src-cell : (p : Pos P s) → BdryCell X P f s (Frm⇒ (SrcIncl X P f s p) (BdryFrm X (Typ P s p)))

    tgt-cell : BdryCell X P f s (Frm⇒ (TgtIncl X P f s) (BdryFrm X f)) 

  data StemCell {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
      (U : Frm (X , P) → Type ℓ)
      (f : Frm X) (s : Src P f) (t : P f)
      (ρ : Pd U (f , s , t)) : Frm (Stem X P f s) → Type ℓ where

    lf-cell : (p : Pos P s) → StemCell X P U f s t ρ (Frm⇒ (SrcIncl X P f s p) (BdryFrm X (Typ P s p)))

    nd-cell : (p : PdPos U ρ) → StemCell X P U f s t ρ (Frm⇒ (NdIncl X P U f s t ρ p) (BdryFrm X (fst (Typ U ρ p))))


  Bdry {zero} X f = tt*
  Bdry {suc n} (X , P) (f , s , t) =
    Stem X P f s , BdryCell X P f s
  
  Stem {zero} X P f s = tt*
  Stem {suc n} (X , P) U (f , s , t) ρ =
    Stem X P f s , StemCell X P U f s t ρ

  BdryFrm {zero} X f = tt*
  BdryFrm {suc n} (X , P) (f , s , t) =
    Frm⇒ (TgtIncl X P f s) (BdryFrm X f) , BdrySrc X P f s , tgt-cell

  StemTgt : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (U : Frm (X , P) → Type ℓ)
    → (f : Frm X) (s : Src P f) (t : P f)
    → (ρ : Pd U (f , s , t))
    → StemCell X P U f s t ρ (Frm⇒ (TgtIncl X P f s) (BdryFrm X f))

  TgtIncl {zero} X P f s = tt*
  TgtIncl {suc n} (X , P) U (f , ._ , .tgt) (lf tgt) = id-map (Stem X P f (η P tgt)) ,
    λ { (src-cell p) → lf-cell p
      ; tgt-cell → {!!}
      } 
  TgtIncl {suc n} (X , P) U (f , ._ , .tgt) (nd src tgt flr brs) = {!!}
    -- id-map (Stem X P f s) ,
    -- (λ { (src-cell p) → lf-cell p
    --    ; tgt-cell     → StemTgt X P U f s t ρ})

  StemTgt X P U f ._ .tgt (lf tgt) = {!lf-cell {U = U} {t = tgt} {ρ = lf tgt} (η-pos P tgt)!}
  StemTgt X P U f ._ .tgt (nd src tgt flr brs) = {!!}

  SrcIncl = {!!}
  
  NdIncl = {!!} 

  BdrySrc = {!!}
  
  -- BdrySrc {zero} X P f s = src-cell tt*
  -- BdrySrc {suc n} X P (f , ._ , ._) (lf tgt) = {!!}
  -- BdrySrc {suc n} X P (f , ._ , ._) (nd src tgt flr brs) = {!!}

