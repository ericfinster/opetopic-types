{-# OPTIONS --no-termination-check #-}

open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType

module Native.Term where

  𝕆Term : ∀ {ℓ n} → 𝕆Type ℓ n → Type ℓ

  TermFrm : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (t : 𝕆Term X)
    → (ο : 𝕆 n) → Frm X ο 

  TermWeb : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (t : 𝕆Term X)
    → {ο : 𝕆 n} (ρ : ℙ ο)
    → Web X (TermFrm X t ο) ρ

  postulate

    Term-Shp : ∀ {ℓ n} (X : 𝕆Type ℓ n)
      → (t : 𝕆Term X)
      → {ο : 𝕆 n} (ρ : ℙ ο)
      → (p : Pos ρ)
      → Shp X (TermWeb X t ρ) p ↦ TermFrm X t (Typ ρ p)
    {-# REWRITE Term-Shp #-}

    Term-η : ∀ {ℓ n} (X : 𝕆Type ℓ n)
      → (t : 𝕆Term X) (ο : 𝕆 n)
      → TermWeb X t (ηₒ ο) ↦ η X (TermFrm X t ο)
    {-# REWRITE Term-η #-}

    Term-μ : ∀ {ℓ n} (X : 𝕆Type ℓ n)
      → (t : 𝕆Term X) (ο : 𝕆 n) (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
      → TermWeb X t (μₒ ρ δ) ↦ μ X (TermWeb X t ρ) (λ p → TermWeb X t (δ p))
    {-# REWRITE Term-μ #-}

  𝕆Term {ℓ} {zero} X = 𝟙 ℓ
  𝕆Term {ℓ} {suc n} (X , P) =
    Σ[ t ∈ 𝕆Term X ]
    ((ο : 𝕆 n) → P (ο , TermFrm X t ο))

  TermFrm {n = zero} X t ο = ●
  TermFrm {n = suc n} (X , P) (s , t) (ο , ρ) =
    TermFrm X s ο , TermWeb X s ρ , (λ p → t (Typ ρ p)) , t ο

  TermWeb {n = zero} X t ρ = ●
  TermWeb {n = suc n} (X , P) (s , t) (lfₒ ο) = lf (t ο)
  TermWeb {n = suc n} (X , P) (s , t) (ndₒ {ο} ρ δ) =
    nd (t ο) ⟪ TermWeb X s ρ , (λ p → t (Typ ρ p)) ⟫
             (λ p → ⟦ TermWeb (X , P) (s , t) (br (δ p)) ⟧)
