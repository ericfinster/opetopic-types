open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType
open import Native.OpetopicTerm
open import Native.Weakening
open import Native.OpetopicMap

module Native.Sigma where

  Σₒ : ∀ {ℓ ℓ↓ n} (X : 𝕆Type ℓ n) (X↓ : 𝕆Type↓ ℓ↓ X)
    → 𝕆Type (ℓ-max ℓ ℓ↓) n

  π₁ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
    → Σₒ X X↓ ⇒ X
    
  π₂ : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
    → 𝕆Term (Σₒ X X↓) (Subst π₁ X↓) 

  Σ-cell : ∀ {ℓ ℓ↓ n} {X : 𝕆Type ℓ n} {X↓ : 𝕆Type↓ ℓ↓ X}
    → (P : Idx X → Type ℓ)
    → (P↓ : {i : Idx X} → P i → Idx↓ X↓ i → Type ℓ↓)
    → Idx (Σₒ X X↓) → Type (ℓ-max ℓ ℓ↓)
  Σ-cell {X = X} {X↓} P P↓ (ο , f) = 
    Σ[ x ∈ P (ο , Frm⇒ π₁ f) ]
    P↓ x (Frm← π₁ X↓ f (Frm↑ π₂ f))
    
  Σₒ ○ ○↓ = ○
  Σₒ (X ∥ P) (X↓ ∥↓ P↓) = Σₒ X X↓ ∥ Σ-cell P P↓ 

  π₁ {X = ○} {○↓} = ■
  π₁ {X = X ∥ P} {X↓ ∥↓ P↓} =
    π₁ {X = X} {X↓} ► fst 

  π₂ {X = ○} {○↓} = ■
  π₂ {X = X ∥ P} {X↓ ∥↓ P↓} =
    π₂ {X = X} {X↓} ► snd
