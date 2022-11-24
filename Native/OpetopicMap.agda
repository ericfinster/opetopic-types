open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType
open import Native.OpetopicTerm
open import Native.Weakening

module Native.OpetopicMap where

  --
  --  Maps of Opetopic Types (as terms)
  --

  _⇒_ : ∀ {ℓ₀ ℓ₁ n} → 𝕆Type ℓ₀ n → 𝕆Type ℓ₁ n
    → Type (ℓ-max ℓ₀ ℓ₁)
  X ⇒ Y = 𝕆Term X (Wk X Y) 

  Frm⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
    → (σ : X ⇒ Y) → {ο : 𝕆 n} → Frm X ο → Frm Y ο 
  Frm⇒ {X = X} {Y} σ f = πFrm X Y (Frm↑ σ f) 
  
  Web⇒ : ∀ {ℓ₀ ℓ₁ n} {X : 𝕆Type ℓ₀ n} {Y : 𝕆Type ℓ₁ n}
    → (σ : X ⇒ Y)   
    → {ο : 𝕆 n} {f : Frm X ο}
    → {ρ : ℙ ο} (ω : Web X f ρ)
    → Web Y (Frm⇒ σ f) ρ
  Web⇒ {X = X} {Y} σ ω = πWeb X Y (Web↑ σ ω) 
