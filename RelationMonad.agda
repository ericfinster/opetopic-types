{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad

module RelationMonad where

  module _ (A : Set) where

    Frmᵣ : Set
    Frmᵣ = ⊤

    Cellᵣ : (f : Frmᵣ) → Set
    Cellᵣ f = A

    Treeᵣ : (f : Frmᵣ) → Set
    Treeᵣ f = A
    
    Posᵣ : {f : Frmᵣ} → Treeᵣ f → Set
    Posᵣ {f} σ = ⊤

    Typᵣ : {f : Frmᵣ} (σ : Treeᵣ f) (p : Posᵣ σ) → Frmᵣ
    Typᵣ {f} σ p = f

    Inhᵣ : {f : Frmᵣ} (σ : Treeᵣ f) (p : Posᵣ σ) → Cellᵣ (Typᵣ σ p)
    Inhᵣ {f} σ p = σ

    ηᵣ : {f : Frmᵣ} (τ : Cellᵣ f) → Treeᵣ f
    ηᵣ {f} τ = τ

    η-posᵣ : {f : Frmᵣ} (τ : Cellᵣ f)
      → Posᵣ (ηᵣ τ)
    η-posᵣ {f} τ = unit

    η-pos-elimᵣ : {f : Frmᵣ} (τ : Cellᵣ f)
      → (X : (p : Posᵣ (ηᵣ τ)) → Set)
      → (η-pos* : X (η-posᵣ τ))
      → (p : Posᵣ (ηᵣ τ)) → X p
    η-pos-elimᵣ τ X η-pos* p = η-pos*
    
    μᵣ : {f : Frmᵣ} (σ : Treeᵣ f)
      → (δ : (p : Posᵣ σ) → Treeᵣ (Typᵣ σ p))
      → Treeᵣ f
    μᵣ σ δ = δ unit

    μ-posᵣ : {f : Frmᵣ} (σ : Treeᵣ f)
      → (δ : (p : Posᵣ σ) → Treeᵣ (Typᵣ σ p))
      → (p : Posᵣ σ) (q : Posᵣ (δ p))
      → Posᵣ (μᵣ σ δ)
    μ-posᵣ σ δ p q = q

    μ-pos-fstᵣ : {f : Frmᵣ} (σ : Treeᵣ f)
      → (δ : (p : Posᵣ σ) → Treeᵣ (Typᵣ σ p))
      → Posᵣ (μᵣ σ δ) → Posᵣ σ
    μ-pos-fstᵣ σ δ p = unit


    μ-pos-sndᵣ : {f : Frmᵣ} (σ : Treeᵣ f)
      → (δ : (p : Posᵣ σ) → Treeᵣ (Typᵣ σ p))
      → (p : Posᵣ (μᵣ σ δ))
      → Posᵣ (δ (μ-pos-fstᵣ σ δ p))
    μ-pos-sndᵣ σ δ p = unit

  postulate

    RelMnd : (A : Set) → 𝕄

    Frm-RelMnd : (A : Set)
      → Frm (RelMnd A) ↦ Frmᵣ A
    {-# REWRITE Frm-RelMnd #-}

    Cell-RelMnd : (A : Set) (f : Frm (RelMnd A))
      → Cell (RelMnd A) f ↦ Cellᵣ A f
    {-# REWRITE Cell-RelMnd #-}

    Tree-RelMnd : (A : Set) (f : Frm (RelMnd A))
      → Tree (RelMnd A) f ↦ Treeᵣ A f
    {-# REWRITE Tree-RelMnd #-}

    Pos-RelMnd : (A : Set) (f : Frm (RelMnd A))
      → (σ : Tree (RelMnd A) f) 
      → Pos (RelMnd A) σ ↦ Posᵣ A σ
    {-# REWRITE Pos-RelMnd #-}

    Typ-RelMnd : (A : Set) (f : Frm (RelMnd A))
      → (σ : Tree (RelMnd A) f) (p : Pos (RelMnd A) σ)
      → Typ (RelMnd A) σ p ↦ Typᵣ A σ p
    {-# REWRITE Typ-RelMnd #-}

    Inh-RelMnd : (A : Set) (f : Frm (RelMnd A))
      → (σ : Tree (RelMnd A) f) (p : Pos (RelMnd A) σ)
      → Inh (RelMnd A) σ p ↦ Inhᵣ A σ p
    {-# REWRITE Inh-RelMnd #-}

    η-RelMnd : (A : Set) {f : Frm (RelMnd A)}
      → (τ : Cell (RelMnd A) f)
      → η (RelMnd A) τ ↦ ηᵣ A τ
    {-# REWRITE η-RelMnd #-}

    --
    -- It appears that because the positions are definitionally
    -- units, that we do not need these extra rules (they even
    -- trigger an internal error).  For now, I'll leave them
    -- commented out, and we'll see if that causes any problems
    -- later on.
    -- 

    -- η-pos-RelMnd : (A : Set) {f : Frm (RelMnd A)}
    --   → (τ : Cell (RelMnd A) f)
    --   → η-pos (RelMnd A) τ ↦ η-posᵣ A τ
    -- {-# REWRITE η-pos-RelMnd #-}
    
    -- η-pos-elim-RelMnd : (A : Set) {f : Frm (RelMnd A)}
    --   → (τ : Cell (RelMnd A) f)
    --   → (X : (p : Pos (RelMnd A) (η (RelMnd A) τ)) → Set)
    --   → (η-pos* : X (η-pos (RelMnd A) τ))
    --   → (p : Pos (RelMnd A) (η (RelMnd A) τ))
    --   → η-pos-elim (RelMnd A) τ X η-pos* p ↦ η-pos-elimᵣ A τ X η-pos* p
    -- {-# REWRITE η-pos-elim-RelMnd #-}

    μ-RelMnd : (A : Set) {f : Frm (RelMnd A)} (σ : Tree (RelMnd A) f)
      → (δ : (p : Pos (RelMnd A) σ) → Tree (RelMnd A) (Typ (RelMnd A) σ p))
      → μ (RelMnd A) σ δ ↦ μᵣ A σ δ
    {-# REWRITE μ-RelMnd #-}
    
    -- μ-pos-RelMnd : (A : Set) {f : Frm (RelMnd A)} (σ : Tree (RelMnd A) f)
    --   → (δ : (p : Pos (RelMnd A) σ) → Tree (RelMnd A) (Typ (RelMnd A) σ p))
    --   → (p : Pos (RelMnd A) σ) (q : Pos (RelMnd A) (δ p))
    --   → μ-pos (RelMnd A) σ δ p q ↦ μ-posᵣ A σ δ p q
    -- {-# REWRITE μ-pos-RelMnd #-}

    -- μ-pos-fst-RelMnd : (A : Set) {f : Frm (RelMnd A)} (σ : Tree (RelMnd A) f)
    --   → (δ : (p : Pos (RelMnd A) σ) → Tree (RelMnd A) (Typ (RelMnd A) σ p))
    --   → (p : Pos (RelMnd A) (μ (RelMnd A) σ δ))
    --   → μ-pos-fst (RelMnd A) σ δ p ↦ μ-pos-fstᵣ A σ δ p
    -- {-# REWRITE μ-pos-fst-RelMnd #-}

    -- μ-pos-snd-RelMnd : (A : Set) {f : Frm (RelMnd A)} (σ : Tree (RelMnd A) f)
    --   → (δ : (p : Pos (RelMnd A) σ) → Tree (RelMnd A) (Typ (RelMnd A) σ p))
    --   → (p : Pos (RelMnd A) (μ (RelMnd A) σ δ))
    --   → μ-pos-snd (RelMnd A) σ δ p ↦ μ-pos-sndᵣ A σ δ p
    -- {-# REWRITE μ-pos-snd-RelMnd #-}
