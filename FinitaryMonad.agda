{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import FiniteUniverse

module FinitaryMonad where

  postulate

    𝕄 : Set

    Idx : 𝕄 → Set
    Cns : (M : 𝕄) (i : Idx M) (P : 𝔽) (ρ : P ⇒ Idx M) → Set 

    η : (M : 𝕄) (i : Idx M) → Cns M i ⊤₀ i

    μ : (M : 𝕄) (i : Idx M)
      → (P : 𝔽) (α : P ⇒ Idx M) (c : Cns M i P α)
      → (Q : P ⇒ 𝔽) (β : π P (λ p → ev Q p ⇒ Idx M)) 
      → (d : π P (λ p → Cns M (ev α p) (ev Q p) (ev β p)))
      → Cns M i (σ P Q) (uncurry₀ {P} {Q} {Idx M} β)

  η-dec : (M : 𝕄) (P : 𝔽) (α : P ⇒ Idx M)
    → π P (λ p → Cns M (ev α p) ⊤₀ (ev α p))
  η-dec M ⊥₀ α = tt
  η-dec M ⊤₀ i = η M i
  η-dec M (P ⊔₀ Q) (α , β) =
    η-dec M P α , η-dec M Q β

  postulate
  
    -- Monad laws
    μ-unit-r : (M : 𝕄) (i : Idx M)
      → (P : 𝔽) (α : P ⇒ Idx M) (c : Cns M i P α)
      → μ M i P α c (cst₀ {P} ⊤₀) α (η-dec M P α) ↦ c 
    {-# REWRITE μ-unit-r #-}

    μ-unit-left : (M : 𝕄) (i : Idx M)
      → (P : 𝔽) (α : P ⇒ Idx M)
      → (c : Cns M i P α)
      → μ M i ⊤₀ i (η M i) P α c ↦ c
    {-# REWRITE μ-unit-left #-}

  --
  --  Implementation of the slice monad
  --

  Idxₛ : (M : 𝕄) → Set
  Idxₛ M = Σ (Idx M) (λ i → Σ 𝔽 (λ P → Σ (P ⇒ Idx M) (λ α → Cns M i P α)))

  data Cnsₛ (M : 𝕄) : Idxₛ M → (Q : 𝔽) → (θ : Q ⇒ Idxₛ M) → Set where

    lf : (i : Idx M) → Cnsₛ M (i , ⊤₀ , i , η M i) ⊥₀ tt 

    nd : (i : Idx M) (P : 𝔽) (α : P ⇒ Idx M) (c : Cns M i P α)
      → (Q : P ⇒ 𝔽) (β : π P (λ p → ev Q p ⇒ Idx M)) 
      → (d : π P (λ p → Cns M (ev α p) (ev Q p) (ev β p)))
      → (R : P ⇒ 𝔽) (δ : π P (λ p → ev R p ⇒ Idxₛ M))
      → (e : π P (λ p → Cnsₛ M (ev α p , ev Q p , ev β p , ev d p) (ev R p) (ev δ p)))
      → Cnsₛ M (i , σ P Q , uncurry₀ {P} {Q} {Idx M} β , μ M i P α c Q β d) (⊤₀ ⊔₀ σ P R)
             ((i , P , α , c) , uncurry₀ {P} {R} {Idxₛ M} δ)


