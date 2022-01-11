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
  
  Cns {n = O} _ _ _ = ⊤ 
  Cns {n = S n} X f ρ = {!!}
  
  Shp {n = O} _ _ _ _ = tt
  Shp {n = S n} X f c p = {!!}

  -- I mean, I guess what I would like to formalize is
  -- the n-th pullback monad.  Maybe that's the right way to say it.

  -- Oh!  Then I think this weird definition that the cns is of a
  -- different dimension is actually correct.

  -- Finally!

  -- data 𝒯r {n : ℕ} : (o : 𝒪 n) (ρ : 𝒫 o) → Set where

  --   lf : (o : 𝒪 n) → 𝒯r o (ηₒ o)
    
  --   nd : (o : 𝒪 n) (ρ : 𝒫 o) 
  --     → (δ : (p : Pos ρ) → 𝒫 (Typ ρ p))
  --     → (ε : (p : Pos ρ) → 𝒯r (Typ ρ p) (δ p))
  --     → 𝒯r o (μₒ ρ δ)



