{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import Pb

module MonadOver where

  postulate

    𝕄↓ : (M : 𝕄) → Set

    Frm↓ : {M : 𝕄} (M↓ : 𝕄↓ M) → Frm M → Set 
    Tree↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Frm M} (f↓ : Frm↓ M↓ f)
      → Tree M f → Set 

    Typ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Frm M} {σ : Tree M f} 
      → {f↓ : Frm↓ M↓ f} (σ↓ : Tree↓ M↓ f↓ σ)
      → (p : Pos M σ) → Frm↓ M↓ (Typ M σ p)

    η↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Frm M} (f↓ : Frm↓ M↓ f)
      → Tree↓ M↓ f↓ (η M f)

    μ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Frm M} {σ : Tree M f}
      → {δ : (p : Pos M σ) → Tree M (Typ M σ p)}
      → {f↓ : Frm↓ M↓ f} (σ↓ : Tree↓ M↓ f↓ σ)
      → (δ↓ : (p : Pos M σ) → Tree↓ M↓ (Typ↓ M↓ σ↓ p) (δ p))
      → Tree↓ M↓ f↓ (μ M σ δ)

    -- typ↓ laws 
    η-pos-typ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Frm M} (f↓ : Frm↓ M↓ f)
      → (p : Pos M (η M f))
      → Typ↓ M↓ (η↓ M↓ f↓) p ↦ f↓
    {-# REWRITE η-pos-typ↓ #-}

    μ-pos-typ↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Frm M} {σ : Tree M f}
      → {δ : (p : Pos M σ) → Tree M (Typ M σ p)}
      → (f↓ : Frm↓ M↓ f) (σ↓ : Tree↓ M↓ f↓ σ)
      → (δ↓ : (p : Pos M σ) → Tree↓ M↓ (Typ↓ M↓ σ↓ p) (δ p))
      → (p : Pos M (μ M σ δ))
      → Typ↓ M↓ (μ↓ M↓ σ↓ δ↓) p ↦ Typ↓ M↓ (δ↓ (μ-pos-fst M σ δ p)) (μ-pos-snd M σ δ p) 
    {-# REWRITE μ-pos-typ↓ #-}
    
    -- μ↓ laws
    μ-unit-right↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Frm M} {σ : Tree M f}
      → {f↓ : Frm↓ M↓ f} (σ↓ : Tree↓ M↓ f↓ σ)
      → μ↓ M↓ σ↓ (λ p → η↓ M↓ (Typ↓ M↓ σ↓ p)) ↦ σ↓
    {-# REWRITE μ-unit-right↓ #-}

    μ-unit-left↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Frm M} {f↓ : Frm↓ M↓ f}
      → {δ : (p : Pos M (η M f)) → Tree M f}
      → (δ↓ : (p : Pos M (η M f)) → Tree↓ M↓ f↓ (δ p))
      → μ↓ M↓ (η↓ M↓ f↓) δ↓ ↦ δ↓ (η-pos M f) 
    {-# REWRITE μ-unit-left↓ #-}
    
    μ-assoc↓ : {M : 𝕄} (M↓ : 𝕄↓ M)
      → {f : Frm M} {σ : Tree M f}
      → {δ : (p : Pos M σ) → Tree M (Typ M σ p)}
      → {ε : (p : Pos M (μ M σ δ)) → Tree M (Typ M (μ M σ δ) p)}
      → {f↓ : Frm↓ M↓ f} (σ↓ : Tree↓ M↓ f↓ σ)
      → (δ↓ : (p : Pos M σ) → Tree↓ M↓ (Typ↓ M↓ σ↓ p) (δ p))
      → (ε↓ : (p : Pos M (μ M σ δ)) → Tree↓ M↓ (Typ↓ M↓ (μ↓ M↓ σ↓ δ↓) p) (ε p))
      → μ↓ M↓ (μ↓ M↓ σ↓ δ↓) ε↓ ↦ μ↓ M↓ σ↓ (λ p → μ↓ M↓ (δ↓ p) (λ q → ε↓ (μ-pos M σ δ p q)))
    {-# REWRITE μ-assoc↓ #-} 
