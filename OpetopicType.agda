{-# OPTIONS --without-K --rewriting --no-positivity-check #-}

open import MiniHoTT
open import Opetopes

module OpetopicType where

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)
  
  Frm : ∀ {ℓ n} → 𝕆 ℓ n → 𝒪 n → Set ℓ
  Cns : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {o : 𝒪 n} (f : Frm X o)
    → 𝒫 o → Set ℓ 
  Shp : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {o : 𝒪 n} (f : Frm X o)
    → {ρ : 𝒫 o} (c : Cns X f ρ)
    → (p : Pos ρ) → Frm X (Typ ρ p) 

  𝕆 ℓ O = ⊤ 
  𝕆 ℓ (S n) = Σ (𝕆 ℓ n) (λ Xₙ → {o : 𝒪 n} → Frm Xₙ o → Set ℓ)
  
  Frm {n = O} X tt = ⊤
  Frm {n = S n} (Xₙ , Xₛₙ) (o , ρ) =
    Σ (Frm Xₙ o) (λ f →
    Σ (Cns Xₙ f ρ) (λ c →
    Σ (Xₛₙ f) (λ x →
    (p : Pos ρ) → Xₛₙ (Shp Xₙ f c p))))

  data Pd {ℓ n} (Xₙ : 𝕆 ℓ n) (Xₛₙ : {o : 𝒪 n} → Frm Xₙ o → Set ℓ)
    : {o : 𝒪 n} {ρ : 𝒫 o}
    → (f : Frm Xₙ o) (c : Cns Xₙ f ρ)
    → (x : Xₛₙ f) (ν : (p : Pos ρ) → Xₛₙ (Shp Xₙ f c p))
    → 𝒯r o ρ 
    → Set ℓ where

    pd-lf : {o : 𝒪 n} (f : Frm Xₙ o) (x : Xₛₙ f)
      → Pd Xₙ Xₛₙ f {!η!} x {!!} (lf o) 

  Cns {n = O} _ _ _ = ⊤ 
  Cns {n = S n} (Xₙ , Xₛₙ) {o , ρ} (f , c , x , ν) τ =
    Pd Xₙ Xₛₙ f c x ν τ
  
  Shp {n = O} _ _ _ _ = tt
  Shp {n = S n} X {o , ρ} f c p = {!!}




