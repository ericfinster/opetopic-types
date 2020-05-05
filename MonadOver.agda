{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad

module MonadOver where


  postulate

    𝕄↓ : (M : 𝕄) → Set

    Frm↓ : {M : 𝕄} (M↓ : 𝕄↓ M) → Frm M → Set

  Typ↓ : {M : 𝕄} (M↓ : 𝕄↓ M) {f : Frm M} (σ : Tree M f) → Set
  Typ↓ {M} M↓ σ = (p : Pos M σ) → Frm↓ M↓ (Typ M σ p)

  postulate
    
    Tree↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Frm M} (f↓ : Frm↓ M↓ f) 
      → (σ : Tree M f) (ϕ : Typ↓ M↓ σ)
      → Set 
    
    η↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Frm M} (f↓ : Frm↓ M↓ f)
      → Tree↓ M↓ f↓ (η M f) (cst f↓) 

    μ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Frm M} {σ : Tree M f}
      → {δ : (p : Pos M σ) → Tree M (Typ M σ p)}
      → {f↓ : Frm↓ M↓ f} (ϕ : Typ↓ M↓ σ) 
      → (ψ : (p : Pos M σ) → Typ↓ M↓ (δ p))
      → (σ↓ : Tree↓ M↓ f↓ σ ϕ)
      → (δ↓ : (p : Pos M σ) → Tree↓ M↓ (ϕ p) (δ p) (ψ p))
      → Tree↓ M↓ f↓ (μ M σ δ) (λ p → ψ (μ-pos-fst M σ δ p) (μ-pos-snd M σ δ p))
    
  --   -- μ↓ laws
  --   μ-unit-right↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → {f : Frm M} {σ : Tree M f}
  --     → {f↓ : Frm↓ M↓ f} (σ↓ : Tree↓ M↓ f↓ σ)
  --     → μ↓ M↓ σ↓ (λ p → η↓ M↓ (Typ↓ M↓ σ↓ p)) ↦ σ↓
  --   {-# REWRITE μ-unit-right↓ #-}

  --   μ-unit-left↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → {f : Frm M} {f↓ : Frm↓ M↓ f}
  --     → {δ : (p : Pos M (η M f)) → Tree M f}
  --     → (δ↓ : (p : Pos M (η M f)) → Tree↓ M↓ f↓ (δ p))
  --     → μ↓ M↓ (η↓ M↓ f↓) δ↓ ↦ δ↓ (η-pos M f) 
  --   {-# REWRITE μ-unit-left↓ #-}
    
  --   μ-assoc↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → {f : Frm M} {σ : Tree M f}
  --     → {δ : (p : Pos M σ) → Tree M (Typ M σ p)}
  --     → {ε : (p : Pos M (μ M σ δ)) → Tree M (Typ M (μ M σ δ) p)}
  --     → {f↓ : Frm↓ M↓ f} (σ↓ : Tree↓ M↓ f↓ σ)
  --     → (δ↓ : (p : Pos M σ) → Tree↓ M↓ (Typ↓ M↓ σ↓ p) (δ p))
  --     → (ε↓ : (p : Pos M (μ M σ δ)) → Tree↓ M↓ (Typ↓ M↓ (μ↓ M↓ σ↓ δ↓) p) (ε p))
  --     → μ↓ M↓ (μ↓ M↓ σ↓ δ↓) ε↓ ↦ μ↓ M↓ σ↓ (λ p → μ↓ M↓ (δ↓ p) (λ q → ε↓ (μ-pos M σ δ p q)))
  --   {-# REWRITE μ-assoc↓ #-} 

  --   --
  --   --  Extension of colors
  --   --
    
  --   Ext : (M : 𝕄) (F↓ : Frm M → Set) → 𝕄↓ M

  --   Frm↓-Ext : (M : 𝕄) (F↓ : Frm M → Set)
  --     → Frm↓ (Ext M F↓) ↦ F↓
  --   {-# REWRITE Frm↓-Ext #-}

  --   Tree↓-Ext : (M : 𝕄) (F↓ : Frm M → Set)
  --     → {f : Frm M} (σ : Tree M f) 
  --     → (f↓ : F↓ f)
  --     → Tree↓ (Ext M F↓) f↓ σ ↦ ((p : Pos M σ) → F↓ (Typ M σ p) )
  --   {-# REWRITE Tree↓-Ext #-}
    
  --   Typ↓-Ext : (M : 𝕄) (F↓ : Frm M → Set)
  --     → {f : Frm M} (σ : Tree M f) 
  --     → (f↓ : F↓ f) (σ↓ : Tree↓ (Ext M F↓) f↓ σ)
  --     → (p : Pos M σ)
  --     → Typ↓ (Ext M F↓) {σ = σ} {f↓ = f↓} σ↓ p ↦ σ↓ p 
  --   {-# REWRITE Typ↓-Ext #-}

  --   η↓-Ext : (M : 𝕄) (F↓ : Frm M → Set)
  --     → {f : Frm M} (f↓ : Frm↓ (Ext M F↓) f)
  --     → η↓ (Ext M F↓) f↓ ↦ (λ _ → f↓)
  --   {-# REWRITE η↓-Ext #-}
    
  --   μ↓-Ext : {M : 𝕄} (F↓ : Frm M → Set)
  --     → {f : Frm M} {σ : Tree M f}
  --     → {δ : (p : Pos M σ) → Tree M (Typ M σ p)}
  --     → {f↓ : Frm↓ (Ext M F↓) f} (σ↓ : Tree↓ (Ext M F↓) f↓ σ)
  --     → (δ↓ : (p : Pos M σ) → Tree↓ (Ext M F↓) (Typ↓ (Ext M F↓) {f↓ = f↓} σ↓ p) (δ p))
  --     → μ↓ (Ext M F↓) {f↓ = f↓} σ↓ δ↓ ↦ (λ p → δ↓ (μ-pos-fst M σ δ p) (μ-pos-snd M σ δ p))
  --   {-# REWRITE μ↓-Ext #-}
  
  --
  -- Slice↓
  --

  Frm↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → Frm (Slice M) → Set
  Frm↓ₛ {M} M↓ (f , σ) = Σ (Frm↓ M↓ f) (λ f↓ → Σ (Typ↓ M↓ σ) (λ ϕ → Tree↓ M↓ f↓ σ ϕ))

  Typ↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
    → {f : Frmₛ M} (σ : Treeₛ M f)
    → Set 
  Typ↓ₛ {M} M↓ σ = (p : Posₛ M σ) → Frm↓ₛ M↓ (Typₛ M σ p)

  data Pd↓ {M : 𝕄} (M↓ : 𝕄↓ M) : {f : Frmₛ M} → Frm↓ₛ M↓ f
    → (σ : Treeₛ M f) → Typ↓ₛ M↓ σ → Set where

    lf↓ : {f : Frm M} (f↓ : Frm↓ M↓ f)
      → Pd↓ M↓ (f↓ , cst f↓ , η↓ M↓ f↓) (lf f) ⊥-elim 
    
    nd↓ : {f : Frm M} {σ : Tree M f}
      → {δ : (p : Pos M σ) → Tree M (Typ M σ p)}
      → {ε : (p : Pos M σ) → Pd M (Typ M σ p , δ p)}
      → {f↓ : Frm↓ M↓ f} (ϕ : Typ↓ M↓ σ) 
      → (ψ : (p : Pos M σ) → Typ↓ M↓ (δ p))
      → (σ↓ : Tree↓ M↓ f↓ σ ϕ)
      → (δ↓ : (p : Pos M σ) → Tree↓ M↓ (ϕ p) (δ p) (ψ p))
      → (χ : (p : Pos M σ) → Typ↓ₛ M↓ (ε p))
      → (ε↓ : (p : Pos M σ) → Pd↓ M↓ (ϕ p , ψ p , δ↓ p) (ε p) (χ p))
      → Pd↓ M↓ (f↓ , (λ p → ψ (μ-pos-fst M σ δ p) (μ-pos-snd M σ δ p)) , μ↓ M↓ ϕ ψ σ↓ δ↓) (nd σ δ ε)
        (λ { (inl unit) → f↓ , ϕ , σ↓ ;
             (inr (p , q)) → χ p q })

  -- Tree↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --   → {f : Frm (Slice M)} (f↓ : Frm↓ₛ M↓ f)
  --   → Tree (Slice M) f → Set 
  -- Tree↓ₛ M↓ (f↓ , σ↓) σ = Pd↓ M↓ (f↓ , σ↓) σ 
  
  -- Typ↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --   → {f : Frm (Slice M)} {σ : Tree (Slice M) f} 
  --   → {f↓ : Frm↓ₛ M↓ f} (σ↓ : Tree↓ₛ M↓ f↓ σ)
  --   → (p : Pos (Slice M) σ) → Frm↓ₛ M↓ (Typ (Slice M) σ p)
  -- Typ↓ₛ M↓ (nd↓ σ↓ δ↓ ε↓) (inl unit) = _ , σ↓
  -- Typ↓ₛ M↓ (nd↓ σ↓ δ↓ ε↓) (inr (p , q)) = Typ↓ₛ M↓ (ε↓ p) q

  -- γ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --   → {f : Frm M} {σ : Tree M f} {ρ : Treeₛ M (f , σ)}
  --   → {δ : (p : Pos M σ) → Tree M (Typ M σ p)}
  --   → {ε : (p : Pos M σ) → Treeₛ M (Typ M σ p , δ p)}
  --   → {f↓ : Frm↓ M↓ f} {σ↓ : Tree↓ M↓ f↓ σ}
  --   → (ρ↓ : Tree↓ₛ M↓ (f↓ , σ↓) ρ)
  --   → (δ↓ : (p : Pos M σ) → Tree↓ M↓ (Typ↓ M↓ σ↓ p) (δ p))
  --   → (ε↓ : (p : Pos M σ) → Tree↓ₛ M↓ (Typ↓ M↓ σ↓ p , δ↓ p) (ε p))
  --   → Tree↓ₛ M↓ (f↓ , μ↓ M↓ σ↓ δ↓) (γ M ρ δ ε) 
  
  -- η↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --   → {f : Frm (Slice M)} (f↓ : Frm↓ₛ M↓ f)
  --   → Tree↓ₛ M↓ f↓ (η (Slice M) f)
  -- η↓ₛ M↓ (f↓ , σ↓) =
  --   let η-dec↓ p = η↓ M↓ (Typ↓ M↓ σ↓ p)
  --       lf-dec↓ p = lf↓ (Typ↓ M↓ σ↓ p)
  --   in nd↓ σ↓ η-dec↓ lf-dec↓

  -- μ↓ₛ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --   → {f : Frm (Slice M)} {σ : Tree (Slice M) f}
  --   → {δ : (p : Pos (Slice M) σ) → Tree (Slice M) (Typ (Slice M) σ p)}
  --   → {f↓ : Frm↓ₛ M↓ f} (σ↓ : Tree↓ₛ M↓ f↓ σ)
  --   → (δ↓ : (p : Pos (Slice M) σ) → Tree↓ₛ M↓ (Typ↓ₛ M↓ {f↓ = f↓} σ↓ p) (δ p))
  --   → Tree↓ₛ M↓ f↓ (μ (Slice M) σ δ)
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

  --   Frm↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → Frm↓ (Slice↓ M↓) ↦ Frm↓ₛ M↓
  --   {-# REWRITE Frm↓-Slice↓ #-}
    
  --   Tree↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → {f : Frm (Slice M)} (f↓ : Frm↓ (Slice↓ M↓) f)
  --     → Tree↓ (Slice↓ M↓) f↓ ↦ Tree↓ₛ M↓ f↓
  --   {-# REWRITE Tree↓-Slice↓ #-}

  --   Typ↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → {f : Frm (Slice M)} {σ : Tree (Slice M) f} 
  --     → {f↓ : Frm↓ₛ M↓ f} (σ↓ : Tree↓ₛ M↓ f↓ σ)
  --     → (p : Pos (Slice M) σ)
  --     → Typ↓ (Slice↓ M↓) σ↓ p ↦ Typ↓ₛ M↓ σ↓ p
  --   {-# REWRITE Typ↓-Slice↓ #-}

  --   η↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → {f : Frm (Slice M)} (f↓ : Frm↓ₛ M↓ f)
  --     → η↓ (Slice↓ M↓) f↓ ↦ η↓ₛ M↓ f↓
  --   {-# REWRITE η↓-Slice↓ #-}

  --   μ↓-Slice↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
  --     → {f : Frm (Slice M)} {σ : Tree (Slice M) f}
  --     → {δ : (p : Pos (Slice M) σ) → Tree (Slice M) (Typ (Slice M) σ p)}
  --     → {f↓ : Frm↓ₛ M↓ f} (σ↓ : Tree↓ₛ M↓ f↓ σ)
  --     → (δ↓ : (p : Pos (Slice M) σ) → Tree↓ₛ M↓ (Typ↓ₛ M↓ {f↓ = f↓} σ↓ p) (δ p))
  --     → μ↓ (Slice↓ M↓) σ↓ δ↓ ↦ μ↓ₛ M↓ σ↓ δ↓
  --   {-# REWRITE μ↓-Slice↓ #-}

