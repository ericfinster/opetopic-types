{-# OPTIONS --without-K --rewriting #-}

open import Base
open import OpetopicType

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

    Rel : (A : Set) → 𝕄

    Frm-Rel : (A : Set)
      → Frm (Rel A) ↦ Frmᵣ A
    {-# REWRITE Frm-Rel #-}

    Cell-Rel : (A : Set) (f : Frm (Rel A))
      → Cell (Rel A) f ↦ Cellᵣ A f
    {-# REWRITE Cell-Rel #-}

    Tree-Rel : (A : Set) (f : Frm (Rel A))
      → Tree (Rel A) f ↦ Treeᵣ A f
    {-# REWRITE Tree-Rel #-}

    Pos-Rel : (A : Set) (f : Frm (Rel A))
      → (σ : Tree (Rel A) f) 
      → Pos (Rel A) σ ↦ Posᵣ A σ
    {-# REWRITE Pos-Rel #-}

    Typ-Rel : (A : Set) (f : Frm (Rel A))
      → (σ : Tree (Rel A) f) (p : Pos (Rel A) σ)
      → Typ (Rel A) σ p ↦ Typᵣ A σ p
    {-# REWRITE Typ-Rel #-}

    Inh-Rel : (A : Set) (f : Frm (Rel A))
      → (σ : Tree (Rel A) f) (p : Pos (Rel A) σ)
      → Inh (Rel A) σ p ↦ Inhᵣ A σ p
    {-# REWRITE Inh-Rel #-}

    η-Rel : (A : Set) {f : Frm (Rel A)}
      → (τ : Cell (Rel A) f)
      → η (Rel A) τ ↦ ηᵣ A τ
    {-# REWRITE η-Rel #-}

    --
    -- It appears that because the positions are definitionally
    -- units, that we do not need these extra rules (they even
    -- trigger an internal error).  For now, I'll leave them
    -- commented out, and we'll see if that causes any problems
    -- later on.
    -- 

    -- η-pos-Rel : (A : Set) {f : Frm (Rel A)}
    --   → (τ : Cell (Rel A) f)
    --   → η-pos (Rel A) τ ↦ η-posᵣ A τ
    -- {-# REWRITE η-pos-Rel #-}
    
    -- η-pos-elim-Rel : (A : Set) {f : Frm (Rel A)}
    --   → (τ : Cell (Rel A) f)
    --   → (X : (p : Pos (Rel A) (η (Rel A) τ)) → Set)
    --   → (η-pos* : X (η-pos (Rel A) τ))
    --   → (p : Pos (Rel A) (η (Rel A) τ))
    --   → η-pos-elim (Rel A) τ X η-pos* p ↦ η-pos-elimᵣ A τ X η-pos* p
    -- {-# REWRITE η-pos-elim-Rel #-}

    μ-Rel : (A : Set) {f : Frm (Rel A)} (σ : Tree (Rel A) f)
      → (δ : (p : Pos (Rel A) σ) → Tree (Rel A) (Typ (Rel A) σ p))
      → μ (Rel A) σ δ ↦ μᵣ A σ δ
    {-# REWRITE μ-Rel #-}
    
    -- μ-pos-Rel : (A : Set) {f : Frm (Rel A)} (σ : Tree (Rel A) f)
    --   → (δ : (p : Pos (Rel A) σ) → Tree (Rel A) (Typ (Rel A) σ p))
    --   → (p : Pos (Rel A) σ) (q : Pos (Rel A) (δ p))
    --   → μ-pos (Rel A) σ δ p q ↦ μ-posᵣ A σ δ p q
    -- {-# REWRITE μ-pos-Rel #-}

    -- μ-pos-fst-Rel : (A : Set) {f : Frm (Rel A)} (σ : Tree (Rel A) f)
    --   → (δ : (p : Pos (Rel A) σ) → Tree (Rel A) (Typ (Rel A) σ p))
    --   → (p : Pos (Rel A) (μ (Rel A) σ δ))
    --   → μ-pos-fst (Rel A) σ δ p ↦ μ-pos-fstᵣ A σ δ p
    -- {-# REWRITE μ-pos-fst-Rel #-}

    -- μ-pos-snd-Rel : (A : Set) {f : Frm (Rel A)} (σ : Tree (Rel A) f)
    --   → (δ : (p : Pos (Rel A) σ) → Tree (Rel A) (Typ (Rel A) σ p))
    --   → (p : Pos (Rel A) (μ (Rel A) σ δ))
    --   → μ-pos-snd (Rel A) σ δ p ↦ μ-pos-sndᵣ A σ δ p
    -- {-# REWRITE μ-pos-snd-Rel #-}
