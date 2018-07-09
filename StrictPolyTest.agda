{-# OPTIONS --without-K --rewriting --strict-poly-monads #-} 

open import HoTT
open import StrictPoly

module StrictPolyTest where
    
  module _ {ℓ} (M : Mnd ℓ) where

    ηρ-test₀ : (i : Idx M)
      → ρ M i (η M i) == ηρ-rec M i
    ηρ-test₀ i = idp

    ηρ-test₁ : (i : Idx M) (p : ρ M i (η M i))
      → p == ηρ-unit
    ηρ-test₁ i p = idp

    μρ-test : (i : Idx M) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (p : ρ M i (μ M i c δ))
      → p == μρ-pair (μρ-f p) (μρ-s p)
    μρ-test i c δ p = idp

    by-rec : (i : Idx M) → ρ M i (η M i) → Type₀
    by-rec i ηρ-unit = ⊤

    red-test : (i : Idx M) (p : ρ M i (η M i))
      → by-rec i p == ⊤
    red-test i p = idp

    slc-ρ-test : (i : Idx (slc M)) (p : ρ (slc M) i (η (slc M) i))
      → p == ηρ (slc M) i
    slc-ρ-test (i , c) true = idp
    slc-ρ-test (i , c) (inr (_ , ()))

    slice-by-rec : (i : Idx (slc M)) (p : ρ (slc M) i (η (slc M) i)) → Type₀
    slice-by-rec i true = ⊤
    slice-by-rec i (inr (_ , ()))
    
    slice-red-test : (i : Idx (slc M)) (p : ρ (slc M) i (η (slc M) i))
      → slice-by-rec i p == ⊤
    slice-red-test i p = {!ρ (slc M) i (η (slc M) i)!}

    slice-mult-test : (i : Idx (slc M)) (c : γ (slc M) i)
      → (δ : (p : ρ (slc M) i c) → γ (slc M) (τ (slc M) i c p))
      → ρ (slc M) i (μ (slc M) i c δ) → Type₀
    slice-mult-test i c δ (μρ-pair p q) = {!!}



    -- Place reduction tests

    -- ηρ-τ : (i : Idx M) (p : ρ M i (η M i))
    --   → τ M i (η M i) p == i
    -- ηρ-τ i p = idp

    -- μρ-τ : (i : Idx M) (c : γ M i)
    --   → (δ : (p : ρ M i c) → γ M (τ M i c p))
    --   → (p : ρ M i (μ M i c δ))
    --   → τ M i (μ M i c δ) p == τ M (τ M i c (μρ-fst M i c δ p)) (δ (μρ-fst M i c δ p)) (μρ-snd M i c δ p)
    -- μρ-τ i c δ p = idp

    -- μρ-fst-β : (i : Idx M) (c : γ M i)
    --   → (δ : (p : ρ M i c) → γ M (τ M i c p)) 
    --   → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀))
    --   → μρ-fst M i c δ (μρ M i c δ p₀ p₁) == p₀
    -- μρ-fst-β i c δ p₀ p₁ = idp

    -- μρ-snd-β : (i : Idx M) (c : γ M i)
    --   → (δ : (p : ρ M i c) → γ M (τ M i c p)) 
    --   → (p₀ : ρ M i c) (p₁ : ρ M (τ M i c p₀) (δ p₀))
    --   → μρ-snd M i c δ (μρ M i c δ p₀ p₁) == p₁
    -- μρ-snd-β i c δ p₀ p₁ = idp

    -- Monad laws

    unit-l : (i : Idx M) (c : γ M i) 
      → μ M i c (λ p → η M (τ M i c p)) == c
    unit-l i c = idp

    unit-r : (i : Idx M)
      → (δ : (p : ρ M i (η M i)) → γ M (τ M i (η M i) p)) 
      → μ M i (η M i) δ == δ (ηρ M i)
    unit-r i δ = idp

    assoc : (i : Idx M) (c : γ M i)
      → (δ : (p : ρ M i c) → γ M (τ M i c p))
      → (ε : (q : ρ M i (μ M i c δ)) → γ M (τ M i (μ M i c δ) q)) 
      → μ M i (μ M i c δ) ε == μ M i c (λ p → μ M (τ M i c p) (δ p) (λ q → ε (μρ M i c δ p q)))
    assoc i c δ ε = idp

