
open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType
open import Native.Term

module Native.Test where

  data _==_ {ℓ} {A : Type ℓ} (a : A) : A → Type ℓ where
    refl : a == a 


  -- Second level doesn't work I think.

  TermShpTest1 : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (t : 𝕆Term X)
    → {ο : 𝕆 n} (ρ : ℙ ο)
    → (p : Pos ρ)
    → Shp X (TermWeb X t ρ) p == TermFrm X t (Typ ρ p)
  TermShpTest1 X t ρ p = refl 

  postulate

    Term-Shp-succ : ∀ {ℓ n} (X : 𝕆Type ℓ n)
      → (P : Idx X → Type ℓ)
      → (s : 𝕆Term X) (t : (ο : 𝕆 n) → P (ο , TermFrm X s ο))
      → {ο : 𝕆 n} (ρ : ℙ ο) (τ : Tr (ο , ρ))
      → (p : TrPos τ)
      → Shp (X , P) (TermWeb (X , P) (s , t) τ) p ↦ TermFrm (X , P) (s , t) (Typ τ p)
    {-# REWRITE Term-Shp-succ #-}

  TermShpTest2 : ∀ {ℓ n} (X : 𝕆Type ℓ (suc n))
    → (t : 𝕆Term X)
    → {ο : 𝕆 (suc n)} (ρ : ℙ ο)
    → (p : Pos ρ)
    → Shp X (TermWeb X t ρ) p == TermFrm X t (Typ ρ p)
  TermShpTest2 X t ρ p = refl 

  TermShpTest3 : ∀ {ℓ n} (X : 𝕆Type ℓ (suc (suc n)))
    → (t : 𝕆Term X)
    → {ο : 𝕆 (suc (suc n))} (ρ : ℙ ο)
    → (p : Pos ρ)
    → Shp X (TermWeb X t ρ) p == TermFrm X t (Typ ρ p)
  TermShpTest3 X t ρ p = {!Shp X (TermWeb X t ρ) p!}

  -- Yeah, so this is really problematic.  The problem is that when
  -- these unfold, 
