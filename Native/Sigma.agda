open import Core.Prelude
open import Native.Opetopes
open import Native.OpetopicType
open import Native.DependentOpetopicType

module Native.Sigma where

  Σₒ : ∀ {ℓ ℓ↓ n} (X : 𝕆Type ℓ n) (X↓ : 𝕆Type↓ ℓ↓ X) → 𝕆Type (ℓ-max ℓ ℓ↓) n

  Idx-fst : ∀ {ℓ ℓ↓ n} (X : 𝕆Type ℓ n) (X↓ : 𝕆Type↓ ℓ↓ X)
    → Idx (Σₒ X X↓) → Idx X 
  Idx-fst X X↓ = {!!} 

  Σₒ ○ ○↓ = ○
  Σₒ (X ∥ P) (X↓ ∥↓ P↓) = Σₒ X X↓ ∥ {!!}

  -- Better would be a *morphism* to X so that we didn't have to
  -- redefine this thing.  Interesting.  What about pairing? 
