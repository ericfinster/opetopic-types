{-# OPTIONS --verbose=rewriting.rewrite:50 --verbose=rewriting.match:60 #-}

open import Core.Prelude
open import Native.NewOpetopes
open import Native.NewOpetopicType
open import Native.NewTerm

module Native.Test where

  --
  --  Testing the rewrites ...
  --
  
  data _==_ {ℓ} {A : Type ℓ} (a : A) : A → Type ℓ where
    refl : a == a 

  TermShpTest1 : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (t : 𝕆Term X)
    → {ο : 𝕆 n} (ρ : ℙ ο)
    → (p : Pos ρ)
    → Shp X (TermWeb X t ρ) p == TermFrm X t (Typ ρ p)
  TermShpTest1 X t ρ p = refl 

  TermShpTest2 : ∀ {ℓ n} (X : 𝕆Type ℓ (suc n))
    → (t : 𝕆Term X)
    → {ο : 𝕆 (suc n)} (ρ : ℙ ο)
    → (p : Pos ρ)
    → Shp X (TermWeb X t ρ) p == TermFrm X t (Typ ρ p)
  TermShpTest2 X t ρ p = refl 

  TermShpTest2' : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (P : Idx X → Type)
    → (s : 𝕆Term X) (t : (ο : 𝕆 n) → P (ο , TermFrm X s ο))
    → {ο : 𝕆 n} (ρ : ℙ ο) (τ : ℙ (ο ∣ ρ))
    → (p : Pos τ)
    → Shp (X ∥ P) (TermWeb (X ∥ P) (s ▸ t) τ) p ==
      TermFrm (X ∥ P) (s ▸ t) (Typ τ p)
  TermShpTest2' X P s t ρ τ p = {!refl!} 

