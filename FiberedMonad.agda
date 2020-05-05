{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import HoTT

module FiberedMonad where

  postulate

    𝕄 : Set

    Idx : 𝕄 → Set
    Cns : (M : 𝕄) (i : Idx M) (P : Set) (τ : P → Idx M) → Set 

    η : (M : 𝕄) (i : Idx M) → Cns M i ⊤ (cst i)

    μ : (M : 𝕄) (i : Idx M)
      → (P : Set) (τ₀ : P → Idx M) (c : Cns M i P τ₀)
      → (Q : P → Set) (τ₁ : (p : P) → Q p → Idx M)
      → (d : (p : P) → Cns M (τ₀ p) (Q p) (τ₁ p))
      → Cns M i (Σ P Q) (uncurry τ₁)
    
  -- Right.  This is the signature of a monad fibered over
  -- the universe.  This should really be how it works.
  -- And Σ needs to be a kind of special type constructor
  -- (like Π) which normalizes definitionally.

  Idxₛ : (M : 𝕄) → Set
  Idxₛ M = Σ (Idx M) (λ i → Σ Set (λ P → Σ (P → Idx M) λ τ → Cns M i P τ))

  data Pd (M : 𝕄) : Idxₛ M → (Q : Set) → (θ : Q → Idxₛ M) → Set where
    lf : (i : Idx M) → Pd M (i , ⊤ , cst i , η M i) ⊥ ⊥-elim
    nd : (i : Idx M)
      → (P : Set) (τ₀ : P → Idx M) (c : Cns M i P τ₀)
      → (Q : P → Set) (τ₁ : (p : P) → Q p → Idx M)
      → (d : (p : P) → Cns M (τ₀ p) (Q p) (τ₁ p))
      → (R : Set) (ζ : R → Idxₛ M)
      → (e : (p : P) → Pd M (τ₀ p , Q p , τ₁ p , d p) R ζ)
      → Pd M (i , Σ P Q , uncurry τ₁ , μ M i P τ₀ c Q τ₁ d) (⊤ ⊔ R)
        (λ { true → i , Σ P Q , uncurry τ₁ , μ M i P τ₀ c Q τ₁ d ; (inr r) → ζ r })

  postulate
  
    Slice : 𝕄 → 𝕄

    Idx-Slice : (M : 𝕄)
      → Idx (Slice M) ↦  Idxₛ M 
    {-# REWRITE Idx-Slice #-}

    Cns-Slice : (M : 𝕄) (i : Idxₛ M) (R : Set) (ζ : R → Idxₛ M)
      → Cns (Slice M) i R ζ ↦ Pd M i R ζ
    {-# REWRITE Cns-Slice #-}

