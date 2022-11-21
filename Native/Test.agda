{-# OPTIONS --verbose=rewriting.rewrite:50 --verbose=rewriting.match:60 #-}

open import Core.Prelude
open import Native.NewOpetopes
open import Native.NewOpetopicType
open import Native.NewTerm

module Native.Test where

  data _==_ {ℓ} {A : Type ℓ} (a : A) : A → Type ℓ where
    refl : a == a 

  -- TermShpTest1 : ∀ {n} (X : 𝕆Type n)
  --   → (t : 𝕆Term X)
  --   → {ο : 𝕆 n} (ρ : ℙ ο)
  --   → (p : Pos ρ)
  --   → Shp X (TermWeb X t ρ) p == TermFrm X t (Typ ρ p)
  -- TermShpTest1 X t ρ p = refl 

  -- TermShpTest2 : ∀ {n} (X : 𝕆Type (suc n))
  --   → (t : 𝕆Term X)
  --   → {ο : 𝕆 (suc n)} (ρ : ℙ ο)
  --   → (p : Pos ρ)
  --   → Shp X (TermWeb X t ρ) p == TermFrm X t (Typ ρ p)
  -- TermShpTest2 X t ρ p = refl 

  TermShpTest2' : ∀ {n} (X : 𝕆Type n)
    → (P : Idx X → Type)
    → (s : 𝕆Term X) (t : (ο : 𝕆 n) → P (ο , TermFrm X s ο))
    → {ο : 𝕆 n} (ρ : ℙ ο) (τ : ℙ (ο ∣ ρ))
    → (p : Pos τ)
    → Shp (X ∥ P) (TermWeb (X ∥ P) (s ▸ t) τ) p ==
      TermFrm (X ∥ P) (s ▸ t) (Typ τ p)
  TermShpTest2' X P s t ρ τ p = refl

  -- TermShpTest3 : ∀ {n} (X : 𝕆Type (suc (suc n)))
  --   → (t : 𝕆Term X)
  --   → {ο : 𝕆 (suc (suc n))} (ρ : ℙ ο)
  --   → (p : Pos ρ)
  --   → Shp X (TermWeb X t ρ) p == TermFrm X t (Typ ρ p)
  -- TermShpTest3 X t ρ p = refl 

  
  -- postulate

  --   Term-Shp-succ : ∀ {ℓ n} (X : 𝕆Type ℓ n)
  --     → (P : Idx X → Type ℓ)
  --     → (s : 𝕆Term X) (t : (ο : 𝕆 n) → P (ο , TermFrm X s ο))
  --     → {ο : 𝕆 n} (ρ : ℙ ο) (τ : Tr (ο , ρ))
  --     → (p : TrPos τ)
  --     → Shp (X , P) (TermWeb (X , P) (s , t) τ) p ↦ TermFrm (X , P) (s , t) (Typ τ p)
  --   {-# REWRITE Term-Shp-succ #-}


  -- TermShpTest3 : ∀ {ℓ n} (X : 𝕆Type ℓ (suc (suc n)))
  --   → (t : 𝕆Term X)
  --   → {ο : 𝕆 (suc (suc n))} (ρ : ℙ ο)
  --   → (p : Pos ρ)
  --   → Shp X (TermWeb X t ρ) p == TermFrm X t (Typ ρ p)
  -- TermShpTest3 X t ρ p = {!Shp X (TermWeb X t ρ) p!}

  -- -- Yeah, so this is really problematic.  The problem is that when
  -- -- these unfold, 
