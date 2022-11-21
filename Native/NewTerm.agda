{-# OPTIONS --type-in-type --verbose=rewriting:10 #-}

open import Core.Prelude
open import Native.NewOpetopes
open import Native.NewOpetopicType

module Native.NewTerm where

  data 𝕆Term : {n : ℕ} → 𝕆Type n → Type 

  TermFrm : ∀ {n} (X : 𝕆Type n)
    → (t : 𝕆Term X)
    → (ο : 𝕆 n) → Frm X ο 

  TermWeb : ∀ {n} (X : 𝕆Type n)
    → (t : 𝕆Term X)
    → {ο : 𝕆 n} (ρ : ℙ ο)
    → Web X (TermFrm X t ο) ρ

  postulate

    Term-Shp : (n : ℕ) (X : 𝕆Type n)
      → (t : 𝕆Term X)
      → {ο : 𝕆 n} (ρ : ℙ ο)
      → (p : Pos ρ)
      → Shp X (TermWeb X t ρ) p ↦ TermFrm X t (Typ ρ p)
    {-# REWRITE Term-Shp #-}

    Term-η : (n : ℕ) (X : 𝕆Type n)
      → (t : 𝕆Term X) (ο : 𝕆 n)
      → TermWeb X t (ηₒ ο) ↦ η X (TermFrm X t ο)
    {-# REWRITE Term-η #-}

    Term-μ : (n : ℕ) (X : 𝕆Type n)
      → (t : 𝕆Term X) (ο : 𝕆 n) (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
      → TermWeb X t (μₒ ρ δ) ↦ μ X (TermWeb X t ρ) (λ p → TermWeb X t (δ p))
    {-# REWRITE Term-μ #-}

  data 𝕆Term where

    □ : 𝕆Term ■

    _▸_ : {n : ℕ} {X : 𝕆Type n}
      → {P : Idx X → Type}
      → (t : 𝕆Term X)
      → (s : (ο : 𝕆 n) → P (ο , TermFrm X t ο))
      → 𝕆Term (X ∥ P)

  TermFrm ■ □ ● = ▣
  TermFrm (X ∥ P) (t ▸ s) (ο ∣ ρ) =
    TermFrm X t ο ►[ s ο , ⟪ TermWeb X t ρ , (λ p → s (Typ ρ p)) ⟫ ]
  
  TermWeb ■ □ objₒ = obj
  TermWeb (X ∥ P) (t ▸ s) (lfₒ ο) = lf (s ο)
  TermWeb (X ∥ P) (t ▸ s) (ndₒ {ο = ο} ρ δ) = 
    nd (s ο) ⟪ TermWeb X t ρ , (λ p → s (Typ ρ p)) ⟫
             (λ p → ⟦ TermWeb (X ∥ P) (t ▸ s) (br (δ p)) ⟧)


  -- --
  -- --  Testing the rewrites ...
  -- --
  
  -- data _==_ {ℓ} {A : Type ℓ} (a : A) : A → Type ℓ where
  --   refl : a == a 

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

  --   -- Term-Shp : (n : ℕ) (X : 𝕆Type n)
  --   --   → (t : 𝕆Term X)
  --   --   → {ο : 𝕆 n} (ρ : ℙ ο)
  --   --   → (p : Pos ρ)
  --   --   → Shp X (TermWeb X t ρ) p ↦ TermFrm X t (Typ ρ p)
  --   -- {-# REWRITE Term-Shp #-}

  -- TermShpTest2' : ∀ {n} (X : 𝕆Type n)
  --   → (P : Idx X → Type)
  --   → (s : 𝕆Term X) (t : (ο : 𝕆 n) → P (ο , TermFrm X s ο))
  --   → {ο : 𝕆 n} (ρ : ℙ ο) (τ : ℙ (ο ∣ ρ))
  --   → (p : Pos τ)
  --   → Shp (X ∥ P) (TermWeb (X ∥ P) (s ▸ t) τ) p ==
  --     TermFrm (X ∥ P) (s ▸ t) (Typ τ p)
  -- TermShpTest2' X P s t ρ τ p = {!refl!} 
