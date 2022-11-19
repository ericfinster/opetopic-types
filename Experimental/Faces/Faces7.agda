--
--  Faces.agda - Faces of an opetopic type
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.OpetopicType
open import Core.OpetopicMap

module Lib.Faces7 where

  Stem : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → 𝕆Type n ℓ

  StemSrcFrm : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f) (p : Pos P s)
    → Frm (Stem X P f s)

  StemTgtFrm : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f) 
    → Frm (Stem X P f s)

  StemPdIncl : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (U : Frm (X , P) → Type ℓ)
    → (f : Frm X) (s : Src P f) (t : P f)
    → (ρ : Pd U (f , s , t)) (p : PdPos U ρ)
    → Stem X P (fst (Typ U ρ p)) (fst (snd (Typ U ρ p))) ⇒ Stem X P f s 

  data StemCell {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
      (U : Frm (X , P) → Type ℓ)
      (f : Frm X) (s : Src P f) (t : P f)
      (ρ : Pd U (f , s , t)) : Frm (Stem X P f s) → Type ℓ 

  Stem {zero} X P f s = tt*
  Stem {suc n} (X , P) U (f , s , t) ρ =
    Stem X P f s , StemCell X P U f s t ρ

  data StemCell {n} {ℓ} X P U f s t ρ where

    lf-cell : (p : Pos P s) → StemCell X P U f s t ρ (StemSrcFrm X P f s p)

    nd-cell : (p : PdPos U ρ) → StemCell X P U f s t ρ
      (Frm⇒ (StemPdIncl X P U f s t ρ p)
            (StemTgtFrm X P (fst (Typ U ρ p))
                            (fst (snd (Typ U ρ p)))))

  StemSrcFrm {zero} X P f s p = tt*
  StemSrcFrm {suc n} (X , P) U (f , s , t) ρ p =
    (Frm⇒ (StemPdIncl X P U f s t ρ p)
       (StemTgtFrm X P (fst (Typ U ρ p)) (fst (snd (Typ U ρ p))))) ,
       {!!} , nd-cell p

  StemTgtFrm = {!!} 

  StemPdIncl = {!!} 
