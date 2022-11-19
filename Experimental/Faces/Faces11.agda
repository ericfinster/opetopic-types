--
--  Faces.agda - Faces of an opetopic type
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat 

open import Core.OpetopicType
open import Core.OpetopicMap
open import Core.Universe

module Experimental.Faces.Faces11 where
  
  Bdry : ∀ {n ℓ} (X : 𝕆Type n ℓ) (f : Frm X)
    → X ⇒ 𝕆U n ℓ
    
  Stem : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → X ⇒ 𝕆U n ℓ 

  data BdryCell {n} {ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
      (f : Frm X) (s : Src P f)
    : {g : Frm X} → (t : P g) → Frm↓ (Frm⇒ (Stem X P f s) g) → Type ℓ 

  data StemCell {n} {ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
      (U : Frm (X , P) → Type ℓ)
      (f : Frm X) (s : Src P f) (t : P f)
      (ρ : Pd U (f , s , t))
    : {g : Frm X} → P g → Frm↓ (Frm⇒ (Stem X P f s) g) → Type ℓ 

  StemSrcFrm : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f) (p : Pos P s)
    → Frm↓ (Frm⇒ (Stem X P f s) (Typ P s p)) 
  
  StemTgtFrm : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → Frm↓ (Frm⇒ (Stem X P f s) f) 

  StemIntFrm : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (U : Frm (X , P) → Type ℓ)
    → (f : Frm X) (s : Src P f) (t : P f)
    → (ρ : Pd U (f , s , t)) (p : PdPos U ρ)
    → Frm↓ (Frm⇒ (Stem X P f s) (fst (Typ U ρ p)) )

  StemIntCnpy : ∀ {n ℓ} (X : 𝕆Type n ℓ) (P : Frm X → Type ℓ)
    → (U : Frm (X , P) → Type ℓ)
    → (f : Frm X) (s : Src P f) (t : P f)
    → (ρ : Pd U (f , s , t)) (p : PdPos U ρ)
    → Src↓ (λ C → C) (Src⇒ (fst (snd (Typ U ρ p))) (Stem X P f s)
        (λ q → StemCell X P U f s t ρ {g = Typ P (fst (snd (Typ U ρ p))) q} (fst (snd (Typ U ρ p)) ⊚ q)))
        (StemIntFrm X P U f s t ρ p) 

  StemBindArg : ∀ {n ℓ} {X : 𝕆Type n ℓ} (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → (ϕ : (p : Pos P s) → Src P (Typ P s p))
    → (p : Pos P s) (q : Pos P (ϕ p))
    → Frm↓ (Frm⇒ (Stem X P f (bind P P f s ϕ)) (Typ P (ϕ p) q)) 

  StemBindBase : ∀ {n ℓ} {X : 𝕆Type n ℓ} (P : Frm X → Type ℓ)
    → (f : Frm X) (s : Src P f)
    → (ϕ : (p : Pos P s) → Src P (Typ P s p))
    → (p : Pos P s) (q : Pos P (ϕ p))
    → Frm↓ (Frm⇒ (Stem X P f (bind P P f s ϕ)) (Typ P s p))

  Bdry {zero} X f = tt*
  Bdry {suc n} (X , P) (f , s , t) =
    Stem X P f s , BdryCell X P f s 
  
  Stem {zero} X P f s = tt*
  Stem {suc n} (X , P) U (f , s , t) ρ =
    Stem X P f s , StemCell X P U f s t ρ

  data BdryCell X P f s where
  
    src-cell : (p : Pos P s) → BdryCell X P f s (s ⊚ p) (StemSrcFrm X P f s p)

    tgt-cell : (t : P f) → BdryCell X P f s t (StemTgtFrm X P f s)

  data StemCell X P U f s t ρ where

    lf-cell : (p : Pos P s) → StemCell X P U f s t ρ (s ⊚ p) (StemSrcFrm X P f s p)

    nd-cell : (p : PdPos U ρ) → StemCell X P U f s t ρ (snd (snd (Typ U ρ p))) (StemIntFrm X P U f s t ρ p)

  StemSrcFrm {zero} X P f s p = tt*
  StemSrcFrm {suc n} (X , P) U (f , s , t) ρ p =
    StemIntFrm X P U f s t ρ p , StemIntCnpy X P U f s t ρ p , nd-cell p

  StemTgtFrm {zero} X P f s = tt*
  StemTgtFrm {suc n} (X , P) U (frm , ._ , ._) (lf tgt) =
    StemSrcFrm X P frm (η P tgt) (η-pos P tgt) ,
    η↓ (λ C → C) {C = StemCell X P U frm (η P tgt) tgt (lf tgt) tgt} (lf-cell (η-pos P tgt)) ,
    lf-cell (η-pos P tgt)
  StemTgtFrm {suc n} (X , P) U (frm , ._ , ._) (nd src tgt flr brs) =
    StemTgtFrm X P frm (bind P P frm src (λ p → lvs (brs ⊛ p))) ,
    {!!} , -- multiply with μ↓ ...  but how? 
    {!!} -- nd-cell nd-here
  
  StemIntFrm = {!!} 
  StemIntCnpy = {!!} 

  StemBindArg = {!!} 
  StemBindBase = {!!} 
