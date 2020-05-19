{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver

module Sigma where

  --
  --  Dependent sum of monads
  --
  
  Frm-Σ : (M : 𝕄) (M↓ : 𝕄↓ M) → Set
  Frm-Σ M M↓ = Σ (Frm M) (Frm↓ M↓)
  
  -- Tree-Σ : (M : 𝕄) (M↓ : 𝕄↓ M)
  --   → (f : Frm-Σ M M↓) → Set
  -- Tree-Σ M M↓ (f , f↓) = Σ (Tree M f) (Tree↓ M↓ f↓)
  
  -- Pos : (M : 𝕄) {f : Frm M}
  --   → Tree M f → Set

  -- Typ : (M : 𝕄) {f : Frm M}
  --   → (σ : Tree M f) (p : Pos M σ)
  --   → Frm M 

  -- η : (M : 𝕄) (f : Frm M)
  --   → Tree M f

  -- η-pos : (M : 𝕄) (f : Frm M)
  --   → Pos M (η M f)

  -- η-pos-elim : (M : 𝕄) (f : Frm M)
  --   → (X : (p : Pos M (η M f)) → Set)
  --   → (η-pos* : X (η-pos M f))
  --   → (p : Pos M (η M f)) → X p

  -- μ : (M : 𝕄) {f : Frm M} (σ : Tree M f)
  --   → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
  --   → Tree M f

  -- μ-pos : (M : 𝕄) {f : Frm M} (σ : Tree M f)
  --   → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
  --   → (p : Pos M σ) (q : Pos M (δ p))
  --   → Pos M (μ M σ δ)

  -- μ-pos-fst : (M : 𝕄) {f : Frm M} (σ : Tree M f)
  --   → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
  --   → Pos M (μ M σ δ) → Pos M σ

  -- μ-pos-snd : (M : 𝕄) {f : Frm M} (σ : Tree M f)
  --   → (δ : (p : Pos M σ) → Tree M (Typ M σ p))
  --   → (p : Pos M (μ M σ δ))
  --   → Pos M (δ (μ-pos-fst M σ δ p))

  postulate

    ΣM : (M : 𝕄) (M↓ : 𝕄↓ M) → 𝕄
    
    Frm-ΣM : (M : 𝕄) (M↓ : 𝕄↓ M)
      → Frm (ΣM M M↓) ↦ Frm-Σ M M↓
    {-# REWRITE Frm-ΣM #-}

    -- Tree-ΣM : (M : 𝕄) (M↓ : 𝕄↓ M)
    --   → (f : Frm-Σ M M↓)
    --   → Tree (ΣM M M↓) f ↦ Tree-Σ M M↓ f
    -- {-# REWRITE Tree-ΣM #-} 

