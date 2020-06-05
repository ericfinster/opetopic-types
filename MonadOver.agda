{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad

module MonadOver where

  postulate

    𝕄↓ : (M : 𝕄) → Set

    Idx↓ : {M : 𝕄} (M↓ : 𝕄↓ M) → Idx M → Set

  Typ↓ : {M : 𝕄} (M↓ : 𝕄↓ M) {f : Idx M} (σ : Cns M f) → Set
  Typ↓ {M} M↓ σ = (p : Pos M σ) → Idx↓ M↓ (Typ M σ p)

  postulate
    
    Cns↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx M} (f↓ : Idx↓ M↓ f) 
      → (σ : Cns M f) (ϕ : Typ↓ M↓ σ)
      → Set 
    
    η↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx M} (f↓ : Idx↓ M↓ f)
      → Cns↓ M↓ f↓ (η M f) (cst f↓) 

    μ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx M} {σ : Cns M f}
      → {δ : (p : Pos M σ) → Cns M (Typ M σ p)}
      → {f↓ : Idx↓ M↓ f} (ϕ : Typ↓ M↓ σ) 
      → (σ↓ : Cns↓ M↓ f↓ σ ϕ)
      → (ψ : Typ↓ M↓ (μ M σ δ))
      → (δ↓ : (p : Pos M σ) → Cns↓ M↓ (ϕ p) (δ p) (λ q → ψ (μ-pos M σ δ p q)))
      → Cns↓ M↓ f↓ (μ M σ δ) ψ 
    
    -- μ↓ laws
    μ-unit-right↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Idx M} {σ : Cns M f}
      → {f↓ : Idx↓ M↓ f} (ϕ : Typ↓ M↓ σ)
      → (σ↓ : Cns↓ M↓ f↓ σ ϕ)
      → μ↓ M↓ {δ = λ p → η M (Typ M σ p)} ϕ σ↓ ϕ (λ p → η↓ M↓ (ϕ p)) ↦ σ↓ 
    {-# REWRITE μ-unit-right↓ #-}

  --   μ-unit-left↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → {f : Idx M} {f↓ : Idx↓ M↓ f}
  --     → {δ : (p : Pos M (η M f)) → Cns M f}
  --     → (δ↓ : (p : Pos M (η M f)) → Cns↓ M↓ f↓ (δ p))
  --     → μ↓ M↓ (η↓ M↓ f↓) δ↓ ↦ δ↓ (η-pos M f) 
  --   {-# REWRITE μ-unit-left↓ #-}
    
  --   μ-assoc↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → {f : Idx M} {σ : Cns M f}
  --     → {δ : (p : Pos M σ) → Cns M (Typ M σ p)}
  --     → {ε : (p : Pos M (μ M σ δ)) → Cns M (Typ M (μ M σ δ) p)}
  --     → {f↓ : Idx↓ M↓ f} (σ↓ : Cns↓ M↓ f↓ σ)
  --     → (δ↓ : (p : Pos M σ) → Cns↓ M↓ (Typ↓ M↓ σ↓ p) (δ p))
  --     → (ε↓ : (p : Pos M (μ M σ δ)) → Cns↓ M↓ (Typ↓ M↓ (μ↓ M↓ σ↓ δ↓) p) (ε p))
  --     → μ↓ M↓ (μ↓ M↓ σ↓ δ↓) ε↓ ↦ μ↓ M↓ σ↓ (λ p → μ↓ M↓ (δ↓ p) (λ q → ε↓ (μ-pos M σ δ p q)))
  --   {-# REWRITE μ-assoc↓ #-} 

  --   --
  --   --  Extension of colors
  --   --
    
  --   Ext : (M : 𝕄) (F↓ : Idx M → Set) → 𝕄↓ M

  --   Idx↓-Ext : (M : 𝕄) (F↓ : Idx M → Set)
  --     → Idx↓ (Ext M F↓) ↦ F↓
  --   {-# REWRITE Idx↓-Ext #-}

  --   Cns↓-Ext : (M : 𝕄) (F↓ : Idx M → Set)
  --     → {f : Idx M} (σ : Cns M f) 
  --     → (f↓ : F↓ f)
  --     → Cns↓ (Ext M F↓) f↓ σ ↦ ((p : Pos M σ) → F↓ (Typ M σ p) )
  --   {-# REWRITE Cns↓-Ext #-}
    
  --   Typ↓-Ext : (M : 𝕄) (F↓ : Idx M → Set)
  --     → {f : Idx M} (σ : Cns M f) 
  --     → (f↓ : F↓ f) (σ↓ : Cns↓ (Ext M F↓) f↓ σ)
  --     → (p : Pos M σ)
  --     → Typ↓ (Ext M F↓) {σ = σ} {f↓ = f↓} σ↓ p ↦ σ↓ p 
  --   {-# REWRITE Typ↓-Ext #-}

  --   η↓-Ext : (M : 𝕄) (F↓ : Idx M → Set)
  --     → {f : Idx M} (f↓ : Idx↓ (Ext M F↓) f)
  --     → η↓ (Ext M F↓) f↓ ↦ (λ _ → f↓)
  --   {-# REWRITE η↓-Ext #-}
    
  --   μ↓-Ext : {M : 𝕄} (F↓ : Idx M → Set)
  --     → {f : Idx M} {σ : Cns M f}
  --     → {δ : (p : Pos M σ) → Cns M (Typ M σ p)}
  --     → {f↓ : Idx↓ (Ext M F↓) f} (σ↓ : Cns↓ (Ext M F↓) f↓ σ)
  --     → (δ↓ : (p : Pos M σ) → Cns↓ (Ext M F↓) (Typ↓ (Ext M F↓) {f↓ = f↓} σ↓ p) (δ p))
  --     → μ↓ (Ext M F↓) {f↓ = f↓} σ↓ δ↓ ↦ (λ p → δ↓ (μ-pos-fst M σ δ p) (μ-pos-snd M σ δ p))
  --   {-# REWRITE μ↓-Ext #-}
  
  --
  -- Slice↓
  --

  Idx↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → Idx (Slice M) → Set
  Idx↓ₛ {M} M↓ (f , σ) = Σ (Idx↓ M↓ f) (λ f↓ → Σ (Typ↓ M↓ σ) (λ ϕ → Cns↓ M↓ f↓ σ ϕ))

  Typ↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {f : Idxₛ M} (σ : Cnsₛ M f)
    → Set 
  Typ↓ₛ {M} M↓ σ = (p : Posₛ M σ) → Idx↓ₛ M↓ (Typₛ M σ p)

  data Pd↓ {M : 𝕄} (M↓ : 𝕄↓ M) : {f : Idxₛ M} → Idx↓ₛ M↓ f
    → (σ : Cnsₛ M f) → Typ↓ₛ M↓ σ → Set where

    lf↓ : {f : Idx M} (f↓ : Idx↓ M↓ f)
      → Pd↓ M↓ (f↓ , cst f↓ , η↓ M↓ f↓) (lf f) ⊥-elim 
    
    -- nd↓ : {f : Idx M} {σ : Cns M f}
    --   → {δ : (p : Pos M σ) → Cns M (Typ M σ p)}
    --   → {ε : (p : Pos M σ) → Pd M (Typ M σ p , δ p)}
    --   → {f↓ : Idx↓ M↓ f} (ϕ : Typ↓ M↓ σ) 
    --   → (ψ : (p : Pos M σ) → Typ↓ M↓ (δ p))
    --   → (σ↓ : Cns↓ M↓ f↓ σ ϕ)
    --   → (δ↓ : (p : Pos M σ) → Cns↓ M↓ (ϕ p) (δ p) (ψ p))
    --   → (χ : (p : Pos M σ) → Typ↓ₛ M↓ (ε p))
    --   → (ε↓ : (p : Pos M σ) → Pd↓ M↓ (ϕ p , ψ p , δ↓ p) (ε p) (χ p))
    --   → Pd↓ M↓ (f↓ , (λ p → ψ (μ-pos-fst M σ δ p) (μ-pos-snd M σ δ p)) , μ↓ M↓ ϕ σ↓ ψ δ↓) (nd σ δ ε)
    --     (λ { (inl unit) → f↓ , ϕ , σ↓ ;
    --          (inr (p , q)) → χ p q })

  Cns↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {f : Idxₛ M} (f↓ : Idx↓ₛ M↓ f) 
    → (σ : Cnsₛ M f) (ϕ : Typ↓ₛ M↓ σ)
    → Set 
  Cns↓ₛ M↓ f↓ σ ϕ = Pd↓ M↓ f↓ σ ϕ 

  -- γ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --   → {f : Idx M} {σ : Cns M f} {ρ : Cnsₛ M (f , σ)}
  --   → {δ : (p : Pos M σ) → Cns M (Typ M σ p)}
  --   → {ε : (p : Pos M σ) → Cnsₛ M (Typ M σ p , δ p)}
  --   → {f↓ : Idx↓ M↓ f} {σ↓ : Cns↓ M↓ f↓ σ}
  --   → (ρ↓ : Cns↓ₛ M↓ (f↓ , σ↓) ρ)
  --   → (δ↓ : (p : Pos M σ) → Cns↓ M↓ (Typ↓ M↓ σ↓ p) (δ p))
  --   → (ε↓ : (p : Pos M σ) → Cns↓ₛ M↓ (Typ↓ M↓ σ↓ p , δ↓ p) (ε p))
  --   → Cns↓ₛ M↓ (f↓ , μ↓ M↓ σ↓ δ↓) (γ M ρ δ ε) 

  -- η↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --   → {f : Idxₛ M} (f↓ : Idx↓ₛ M↓ f)
  --   → Cns↓ₛ M↓ f↓ (ηₛ M f) (λ { true → f↓ })
  -- η↓ₛ M↓ (f↓ , ϕ↓ , σ↓) =
  --   let η-dec↓ p = η↓ M↓ (ϕ↓ p)
  --       lf-dec↓ p = lf↓ (ϕ↓ p) 
  --   in {!nd↓ ? ? σ↓ η-dec↓ ? lf-dec↓ !}

  -- μ↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --   → {f : Idx (Slice M)} {σ : Cns (Slice M) f}
  --   → {δ : (p : Pos (Slice M) σ) → Cns (Slice M) (Typ (Slice M) σ p)}
  --   → {f↓ : Idx↓ₛ M↓ f} (σ↓ : Cns↓ₛ M↓ f↓ σ)
  --   → (δ↓ : (p : Pos (Slice M) σ) → Cns↓ₛ M↓ (Typ↓ₛ M↓ {f↓ = f↓} σ↓ p) (δ p))
  --   → Cns↓ₛ M↓ f↓ (μ (Slice M) σ δ)
  -- μ↓ₛ M↓ (lf↓ f↓) κ↓ = lf↓ f↓
  -- μ↓ₛ M↓ (nd↓ σ↓ δ↓ ε↓) κ↓ = 
  --   let w↓ = κ↓ (inl unit)
  --       κ↓↑ p q = κ↓ (inr (p , q))
  --       ψ↓ p = μ↓ₛ M↓ (ε↓ p) (κ↓↑ p) 
  --   in γ↓ M↓ w↓ δ↓ ψ↓
  
  -- γ↓ {M = M} M↓ (lf↓ {f = f} f↓) ϕ↓ ψ↓ = ψ↓ (η-pos M f)
  -- γ↓ {M = M} M↓ (nd↓ {σ = σ} {δ = δ} σ↓ δ↓ ε↓) ϕ↓ ψ↓ =
  --   let ϕ↓↑ p q = ϕ↓ (μ-pos M σ δ p q)
  --       ψ↓↑ p q = ψ↓ (μ-pos M σ δ p q)
  --       δ↓↑ p = μ↓ M↓ (δ↓ p) (ϕ↓↑ p)
  --       ε↓↑ p = γ↓ M↓ (ε↓ p) (ϕ↓↑ p) (ψ↓↑ p)
  --   in nd↓ σ↓ δ↓↑ ε↓↑

  -- postulate

  --   Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M) → 𝕄↓ (Slice M)

  --   Idx↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → Idx↓ (Slice↓ M↓) ↦ Idx↓ₛ M↓
  --   {-# REWRITE Idx↓-Slice↓ #-}
    
  --   Cns↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → {f : Idx (Slice M)} (f↓ : Idx↓ (Slice↓ M↓) f)
  --     → Cns↓ (Slice↓ M↓) f↓ ↦ Cns↓ₛ M↓ f↓
  --   {-# REWRITE Cns↓-Slice↓ #-}

  --   Typ↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → {f : Idx (Slice M)} {σ : Cns (Slice M) f} 
  --     → {f↓ : Idx↓ₛ M↓ f} (σ↓ : Cns↓ₛ M↓ f↓ σ)
  --     → (p : Pos (Slice M) σ)
  --     → Typ↓ (Slice↓ M↓) σ↓ p ↦ Typ↓ₛ M↓ σ↓ p
  --   {-# REWRITE Typ↓-Slice↓ #-}

  --   η↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → {f : Idx (Slice M)} (f↓ : Idx↓ₛ M↓ f)
  --     → η↓ (Slice↓ M↓) f↓ ↦ η↓ₛ M↓ f↓
  --   {-# REWRITE η↓-Slice↓ #-}

  --   μ↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → {f : Idx (Slice M)} {σ : Cns (Slice M) f}
  --     → {δ : (p : Pos (Slice M) σ) → Cns (Slice M) (Typ (Slice M) σ p)}
  --     → {f↓ : Idx↓ₛ M↓ f} (σ↓ : Cns↓ₛ M↓ f↓ σ)
  --     → (δ↓ : (p : Pos (Slice M) σ) → Cns↓ₛ M↓ (Typ↓ₛ M↓ {f↓ = f↓} σ↓ p) (δ p))
  --     → μ↓ (Slice↓ M↓) σ↓ δ↓ ↦ μ↓ₛ M↓ σ↓ δ↓
  --   {-# REWRITE μ↓-Slice↓ #-}

