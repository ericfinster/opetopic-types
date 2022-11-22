open import Core.Prelude
open import Native.NewOpetopes
open import Native.NewOpetopicType

module Native.NewTerm where

  data 𝕆Term {ℓ : Level} : {n : ℕ} → 𝕆Type ℓ n → Type 

  TermFrm : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (t : 𝕆Term X)
    → (ο : 𝕆 n) → Frm X ο 

  TermWeb : ∀ {ℓ n} (X : 𝕆Type ℓ n)
    → (t : 𝕆Term X)
    → {ο : 𝕆 n} (ρ : ℙ ο)
    → Web X (TermFrm X t ο) ρ

  postulate

    Term-Shp : ∀ {ℓ} (n : ℕ) (X : 𝕆Type ℓ n)
      → (t : 𝕆Term X)
      → {ο : 𝕆 n} (ρ : ℙ ο)
      → (p : Pos ρ)
      → Shp X (TermWeb X t ρ) p ↦ TermFrm X t (Typ ρ p)
    {-# REWRITE Term-Shp #-}

    Term-η : ∀ {ℓ} (n : ℕ) (X : 𝕆Type ℓ n)
      → (t : 𝕆Term X) (ο : 𝕆 n)
      → TermWeb X t (ηₒ ο) ↦ η X (TermFrm X t ο)
    {-# REWRITE Term-η #-}

    Term-μ : ∀ {ℓ} (n : ℕ) (X : 𝕆Type ℓ n)
      → (t : 𝕆Term X) (ο : 𝕆 n) (ρ : ℙ ο)
      → (δ : (p : Pos ρ) → ℙ (Typ ρ p))
      → TermWeb X t (μₒ ρ δ) ↦ μ X (TermWeb X t ρ) (λ p → TermWeb X t (δ p))
    {-# REWRITE Term-μ #-}

  {-# NO_UNIVERSE_CHECK #-}
  data 𝕆Term {ℓ} where

    □ : 𝕆Term ■

    _▸_ : {n : ℕ} {X : 𝕆Type ℓ n}
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


