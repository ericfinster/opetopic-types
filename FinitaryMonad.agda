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

  postulate
  
    -- Free monad multiplication 
    γₛ : (M : 𝕄) (i : Idx M)
      → (P : 𝔽) (α : P ⇒ Idx M) (c : Cns M i P α)
      → (Q : P ⇒ 𝔽) (β : π P (λ p → ev Q p ⇒ Idx M))
      → (d : π P (λ p → Cns M (ev α p) (ev Q p) (ev β p)))
      → (R : 𝔽) (θ : R ⇒ Idxₛ M) (e : Cnsₛ M (i , P , α , c) R θ)
      → (O : P ⇒ 𝔽) (ζ : π P (λ p → ev O p ⇒ Idxₛ M))
      → (f : π P (λ p → Cnsₛ M (ev α p , ev Q p , ev β p , ev d p) (ev O p) (ev ζ p)))
      → Cnsₛ M (i , σ P Q , uncurry₀ {P} {Q} {Idx M} β , μ M i P α c Q β d)
             (R ⊔₀ (σ P O)) (θ , uncurry₀ {P} {O} {Idxₛ M} ζ)

  lf-dec : (M : 𝕄) (P : 𝔽) (α : P ⇒ Idx M)
    → π P (λ p → Cnsₛ M (ev α p , ⊤₀ , ev α p , ev (η-dec M P α) p) ⊥₀ tt)
  lf-dec M ⊥₀ α = tt
  lf-dec M ⊤₀ i = lf i
  lf-dec M (P ⊔₀ Q) (α , β) =
    lf-dec M P α , lf-dec M Q β

  ηₛ : (M : 𝕄) (i : Idxₛ M) → Cnsₛ M i ⊤₀ i
  ηₛ M (i , P , α , c) =
    {!nd i P α c (cst₀ {P} ⊤₀) α (η-dec M P α) (cst₀ {P} ⊥₀) (cst₀ {P} tt) (lf-dec M P α)!}

  -- Goal: Cnsₛ M (i , P , α , c) ⊤₀ (i , P , α , c)
  -- Have: Cnsₛ M (i , P , α , c) (⊤₀ ⊔₀ σ P (cst₀ ⊥₀))
  --       ((i , P , α , c) , uncurry₀ (cst₀ tt))

  -- μₛ : (M : 𝕄) (i : Idxₛ M)
  --   → (P : 𝕌) (ρ : El P → Idxₛ M) (c : Cnsₛ M i P ρ)
  --   → (Q : El P → 𝕌) (σ : (p : El P) → El (Q p) → Idxₛ M)
  --   → (d : (p : El P) → Cnsₛ M (ρ p) (Q p) (σ p))
  --   → Cnsₛ M i (Σₛ P Q) (uncurryₛ σ)
  -- μₛ M ._ ._ ._ (lf i) Q₁ σ₁ d₁ = {!lf i!}
  -- μₛ M ._ ._ ._ (nd i P ρ c Q σ d R τ e) T θ f =
  --   let T₀ = T (inlₛ ⊤ₛ (Σₛ P R) ttₛ)
  --       θ₀ = θ (inlₛ ⊤ₛ (Σₛ P R) ttₛ)
  --       f₀ = f (inlₛ ⊤ₛ (Σₛ P R) ttₛ)
  --       T₁ p r = T (inrₛ ⊤ₛ (Σₛ P R) (prₛ P R p r))
  --       θ₁ p r = θ (inrₛ ⊤ₛ (Σₛ P R) (prₛ P R p r))
  --       f₁ p r = f (inrₛ ⊤ₛ (Σₛ P R) (prₛ P R p r))
  --       U p = Σₛ (R p) (T₁ p)
  --       κ p = uncurryₛ (θ₁ p)
  --       ψ p = μₛ M (ρ p , Q p , σ p , d p) (R p) (τ p) (e p) (T₁ p) (θ₁ p) (f₁ p)
  --   in {!γₛ M i P ρ c Q σ d T₀ θ₀ f₀ U κ ψ!}

