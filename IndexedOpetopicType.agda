{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT
open import Opetopes

module OpetopicType where

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  
  Frm : ∀ {ℓ n} → 𝕆 ℓ n → 𝒪 n → Set ℓ
  Cns : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {o : 𝒪 n} (f : Frm X o)
    → 𝒫 o → Set ℓ 
  Shp : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {o : 𝒪 n} {f : Frm X o}
    → {ρ : 𝒫 o} (c : Cns X f ρ)
    → (p : Pos ρ) → Frm X (Typ ρ p) 

  postulate

    η : ∀ {n ℓ} (X : 𝕆 ℓ n)
      → {o : 𝒪 n} (f : Frm X o)
      → Cns X f (ηₒ o)

    μ : ∀ {n ℓ} (X : 𝕆 ℓ n)
      → {o : 𝒪 n} {f : Frm X o}
      → {ρ : 𝒫 o} (c : Cns X f ρ)
      → {ι : (p : Pos ρ) → 𝒫 (Typ ρ p)}
      → (κ : (p : Pos ρ) → Cns X (Shp X c p) (ι p))
      → Cns X f (μₒ ρ ι)

  postulate

    η-pos-shp : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {o : 𝒪 n} (f : Frm X o)
      → (p : Pos (ηₒ o))
      → Shp X (η X f) p ↦ f
    {-# REWRITE η-pos-shp #-}

    μ-pos-shp : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {o : 𝒪 n} {f : Frm X o}
      → {ρ : 𝒫 o} (c : Cns X f ρ)
      → {ι : (p : Pos ρ) → 𝒫 (Typ ρ p)}
      → (κ : (p : Pos ρ) → Cns X (Shp X c p) (ι p))
      → (p : Pos (μₒ ρ ι))
      → Shp X (μ X c κ) p ↦ Shp X (κ (μₒ-pos-fst ρ ι p)) (μₒ-pos-snd ρ ι p)
    {-# REWRITE μ-pos-shp #-} 

  𝕆 ℓ O = ⊤ 
  𝕆 ℓ (S n) = Σ (𝕆 ℓ n) (λ Xₙ → {o : 𝒪 n} → Frm Xₙ o → Set ℓ)
  
  Frm {n = O} X tt = ⊤
  Frm {n = S n} (Xₙ , Xₛₙ) (o , ρ) =
    Σ (Frm Xₙ o) (λ f →
    Σ (Cns Xₙ f ρ) (λ c →
    Σ (Xₛₙ f) (λ x →
    (p : Pos ρ) → Xₛₙ (Shp Xₙ c p))))

  data Pd {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : {o : 𝒪 n} → Frm Xₙ o → Set ℓ)
    : {o : 𝒪 n} {ρ : 𝒫 o}
    → (f : Frm Xₙ o) (c : Cns Xₙ f ρ)
    → (x : Xₛₙ f) (ν : (p : Pos ρ) → Xₛₙ (Shp Xₙ c p))
    → 𝒯r o ρ 
    → Set ℓ where

    pd-lf : {o : 𝒪 n} (f : Frm Xₙ o) (x : Xₛₙ f)
      → Pd Xₙ Xₛₙ f (η Xₙ f) x (cst x) (lf o) 

    pd-nd : {o : 𝒪 n} {ρ : 𝒫 o}
      → {δₒ : (p : Pos ρ) → 𝒫 (Typ ρ p)}
      → {εₒ : (p : Pos ρ) → 𝒯r (Typ ρ p) (δₒ p)}
      → (f : Frm Xₙ o) (c : Cns Xₙ f ρ)
      → (κ : (p : Pos ρ) → Cns Xₙ (Shp Xₙ c p) (δₒ p))
      → (x : Xₛₙ f) (ν₀ : (p : Pos ρ) → Xₛₙ (Shp Xₙ c p))
      → (ν₁ : (p : Pos ρ) (q : Pos (δₒ p)) → Xₛₙ (Shp Xₙ (κ p) q))
      → Pd Xₙ Xₛₙ f (μ Xₙ c κ) x (λ p → ν₁ (μₒ-pos-fst ρ δₒ p) (μₒ-pos-snd ρ δₒ p)) (nd o ρ δₒ εₒ) 

  Cns {n = O} _ _ _ = ⊤ 
  Cns {n = S n} (Xₙ , Xₛₙ) {o , ρ} (f , c , x , ν) τ =
    Pd Xₙ Xₛₙ f c x ν τ
  
  Shp {n = O} _ _ _ = tt
  Shp {n = S n} X {o , ρ} c p = {!!}




