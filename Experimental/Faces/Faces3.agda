--
--  Faces.agda - Faces of an opetopic type
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.OpetopicType
open import Core.OpetopicMap

module Lib.Faces3 where

  Bdry : ∀ {n ℓ} (X : 𝕆Type n ℓ) (f : Frm X)
    → 𝕆Type n ℓ 

  Stem : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → 𝕆Type n ℓ

  data StemCell {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
      (U : Frm (X , P) → Type ℓ) : 
      (f : Frm X) (s : Src P f) (t : P f)
      (ρ : Pd U (f , s , t)) → Frm (Stem X P f s) → Type ℓ 

  data BdryCell {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    (f : Frm X) (s : Src P f) : Frm (Stem X P f s) → Type ℓ 


  SrcIncl : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f) (p : Pos P s)
    → Bdry X (Typ P s p) ⇒ Stem X P f s

  TgtIncl : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → Bdry X f ⇒ Stem X P f s

  BdryFrm : ∀ {n ℓ} (X : 𝕆Type n ℓ) (f : Frm X) → Frm (Bdry X f)

  --
  --  Data declarations
  --

  data StemCell {n} {ℓ} X P U where

    lf-cell : (f : Frm X) (t : P f)
      → StemCell X P U f (η P t) t (lf t) (Frm⇒ (TgtIncl X P f (η P t)) (BdryFrm X f))

    nd-cell-here : {f : Frm X} (src : Src P f) (tgt : P f) 
      → (flr : U (f , src , tgt))
      → (brs : Dec (Branch U) {f = f} src)
      → StemCell X P U f (canopy U {s = src} brs) tgt (nd src tgt flr brs)
          (Frm⇒ (TgtIncl X P f (canopy U {s = src} brs)) (BdryFrm X f))

    -- nd-cell-there : {f : Frm X} {src : Src P f} {tgt : P f}
    --    → {flr : U (f , src , tgt)}
    --    → {brs : Dec (Branch U) {f = f} src}
    --    → (p : Pos P src)
    --    → (sf : Frm (Stem X P (Typ P src p) (lvs (brs ⊛ p))))
    --    → StemCell X P U (Typ P src p) (lvs (brs ⊛ p)) (src ⊚ p) (br (brs ⊛ p)) sf 
    --    → StemCell X P U f (canopy U {s = src} brs) tgt (nd src tgt flr brs)
    --        (Frm⇒ (StemPromote X P U src tgt flr brs p) sf) 


  data BdryCell {n} {ℓ} X P f s where

    src-cell : (p : Pos P s) → BdryCell X P f s (Frm⇒ (SrcIncl X P f s p) (BdryFrm X (Typ P s p)))

    tgt-cell : BdryCell X P f s (Frm⇒ (TgtIncl X P f s) (BdryFrm X f)) 


  Stem {zero} X P f s = tt*
  Stem {suc n} (X , P) U (f , s , t) ρ =
    Stem X P f s , StemCell X P U f s t ρ

  Bdry {zero} X f = tt*
  Bdry {suc n} (X , P) (f , s , t) =
    Stem X P f s , BdryCell X P f s

  cell-map : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (U : Frm (X , P) → Type ℓ) 
    → (f : Frm X) (s : Src P f) (t : P f)
    → (ρ : Pd U (f , s , t))
    → (sf : Frm (Stem X P f s)) → BdryCell X P f s sf → StemCell X P U f s t ρ sf
  cell-map X P U f s t ρ ._ (src-cell p) = {!!}
  cell-map X P U f s t ρ ._ tgt-cell = {!!}

  TgtIncl {zero} X P f s = tt*
  TgtIncl {suc n} (X , P) U (f , s , t) ρ =
    id-map (Stem X P f s) , {!!}

  SrcIncl = {!!}


  BdryFrm = {!!} 
