--
--  Faces.agda - Faces of an opetopic type
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.OpetopicType
open import Core.OpetopicMap

module Lib.Faces8 where

  Stem : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → 𝕆Type n ℓ

  data StemCell {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
      (U : Frm (X , P) → Type ℓ) : 
      (f : Frm X) (s : Src P f) (t : P f)
      (ρ : Pd U (f , s , t)) → Frm (Stem X P f s) → Type ℓ 

  StemFrm : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → Frm (Stem X P f s)

  StemSrc : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (U : Frm (X , P) → Type ℓ)  
    → (f : Frm X) (s : Src P f) (t : P f)
    → (ρ : Pd U (f , s , t))
    → Src (StemCell X P U f s t ρ) (StemFrm X P f s)

  StemTgt : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (U : Frm (X , P) → Type ℓ)  
    → (f : Frm X) (s : Src P f) (t : P f)
    → (ρ : Pd U (f , s , t))
    → StemCell X P U f s t ρ (StemFrm X P f s)

  StemPromote : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (U : Frm (X , P) → Type ℓ)  
    → {f : Frm X} (src : Src P f) (tgt : P f)
    → (flr : U (f , src , tgt))
    → (brs : Dec (Branch U) {f = f} src)
    → (p : Pos P src)
    → Stem X P (Typ P src p) (lvs (brs ⊛ p)) ⇒ Stem X P f (canopy U brs)

  data StemCell {n} {ℓ} X P U where

    lf-cell : (f : Frm X) (t : P f)
      → StemCell X P U f (η P t) t (lf t) (StemFrm X P f (η P t)) 

    nd-cell-here : {f : Frm X} (src : Src P f) (tgt : P f) 
      → (flr : U (f , src , tgt))
      → (brs : Dec (Branch U) {f = f} src)
      → StemCell X P U f (canopy U {s = src} brs) tgt (nd src tgt flr brs)
          (StemFrm X P f (canopy U {s = src} brs)) 

    nd-cell-there : {f : Frm X} {src : Src P f} {tgt : P f}
       → {flr : U (f , src , tgt)}
       → {brs : Dec (Branch U) {f = f} src}
       → (p : Pos P src)
       → (sf : Frm (Stem X P (Typ P src p) (lvs (brs ⊛ p))))
       → StemCell X P U (Typ P src p) (lvs (brs ⊛ p)) (src ⊚ p) (br (brs ⊛ p)) sf 
       → StemCell X P U f (canopy U {s = src} brs) tgt (nd src tgt flr brs)
           (Frm⇒ (StemPromote X P U src tgt flr brs p) sf) 

  Stem {zero} X P f s = tt*
  Stem {suc n} (X , P) U (f , s , t) ρ =
    Stem X P f s , StemCell X P U f s t ρ

  StemFrm {zero} X P f s = tt*
  StemFrm {suc n} (X , P) U (f , s , t) ρ =
    StemFrm X P f s , StemSrc X P U f s t ρ , StemTgt X P U f s t ρ

  StemTgt X P U f ._ .tgt (lf {frm} tgt) = lf-cell frm tgt
  StemTgt X P U f ._ .tgt (nd {frm} src tgt flr brs) = nd-cell-here src tgt flr brs

  StemSrc X P U f ._ .tgt (lf {frm} tgt) =
    η (StemCell X P U f (η P tgt) tgt (lf tgt)) (lf-cell frm tgt)
  StemSrc X P U f ._ .tgt (nd {frm} src tgt flr brs) = 
    μ (StemCell X P U f (canopy U {s = src} brs) tgt (nd src tgt flr brs))
      {!StemFrm X P frm src!}

  StemPromote X P U src tgt flr brs p = {!!} 

