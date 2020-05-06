{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad

module IdentityMonad where

  module _ (A : Set) where

    Frmᵢ : Set
    Frmᵢ = A

    Treeᵢ : (f : Frmᵢ) → Set
    Treeᵢ a = ⊤
    
    Posᵢ : {f : Frmᵢ} → Treeᵢ f → Set
    Posᵢ {a} _ = ⊤

    Typᵢ : {f : Frmᵢ} (σ : Treeᵢ f) (p : Posᵢ {f = f} σ) → Frmᵢ
    Typᵢ {a} _ _ = a

    -- ηᵢ : {f : Frmᵢ} (τ : Cellᵢ f) → Treeᵢ f
    -- ηᵢ {f} τ = τ

  --   η-posᵢ : {f : Frmᵢ} (τ : Cellᵢ f)
  --     → Posᵢ (ηᵢ τ)
  --   η-posᵢ {f} τ = unit

  --   η-pos-elimᵢ : {f : Frmᵢ} (τ : Cellᵢ f)
  --     → (X : (p : Posᵢ (ηᵢ τ)) → Set)
  --     → (η-pos* : X (η-posᵢ τ))
  --     → (p : Posᵢ (ηᵢ τ)) → X p
  --   η-pos-elimᵢ τ X η-pos* p = η-pos*
    
  --   μᵢ : {f : Frmᵢ} (σ : Treeᵢ f)
  --     → (δ : (p : Posᵢ σ) → Treeᵢ (Typᵢ σ p))
  --     → Treeᵢ f
  --   μᵢ σ δ = δ unit

  --   μ-posᵢ : {f : Frmᵢ} (σ : Treeᵢ f)
  --     → (δ : (p : Posᵢ σ) → Treeᵢ (Typᵢ σ p))
  --     → (p : Posᵢ σ) (q : Posᵢ (δ p))
  --     → Posᵢ (μᵢ σ δ)
  --   μ-posᵢ σ δ p q = q

  --   μ-pos-fstᵢ : {f : Frmᵢ} (σ : Treeᵢ f)
  --     → (δ : (p : Posᵢ σ) → Treeᵢ (Typᵢ σ p))
  --     → Posᵢ (μᵢ σ δ) → Posᵢ σ
  --   μ-pos-fstᵢ σ δ p = unit


  --   μ-pos-sndᵢ : {f : Frmᵢ} (σ : Treeᵢ f)
  --     → (δ : (p : Posᵢ σ) → Treeᵢ (Typᵢ σ p))
  --     → (p : Posᵢ (μᵢ σ δ))
  --     → Posᵢ (δ (μ-pos-fstᵢ σ δ p))
  --   μ-pos-sndᵢ σ δ p = unit

  postulate

    IdMnd : (A : Set) → 𝕄

    Frm-IdMnd : (A : Set)
      → Frm (IdMnd A) ↦ Frmᵢ A
    {-# REWRITE Frm-IdMnd #-}

    Tree-IdMnd : (A : Set) (f : Frm (IdMnd A))
      → Tree (IdMnd A) f ↦ Treeᵢ A f
    {-# REWRITE Tree-IdMnd #-}

    Pos-IdMnd : (A : Set) (f : Frm (IdMnd A))
      → (σ : Tree (IdMnd A) f) 
      → Pos (IdMnd A) {f = f} σ ↦ Posᵢ A {f = f}  σ
    {-# REWRITE Pos-IdMnd #-}

    -- Typ-IdMnd : (A : Set) (f : Frm (IdMnd A))
    --   → (σ : Tree (IdMnd A) f) (p : Pos (IdMnd A) {f = f} σ)
    --   → Typ (IdMnd A) {f = f} σ p ↦ Typᵢ A {f = f} σ p
    -- {-# REWRITE Typ-IdMnd #-}

  --   η-IdMnd : (A : Set) {f : Frm (IdMnd A)}
  --     → (τ : Cell (IdMnd A) f)
  --     → η (IdMnd A) τ ↦ ηᵢ A τ
  --   {-# REWRITE η-IdMnd #-}

  --   --
  --   -- It appears that because the positions are definitionally
  --   -- units, that we do not need these extra rules (they even
  --   -- trigger an internal error).  For now, I'll leave them
  --   -- commented out, and we'll see if that causes any problems
  --   -- later on.
  --   -- 

  --   -- η-pos-IdMnd : (A : Set) {f : Frm (IdMnd A)}
  --   --   → (τ : Cell (IdMnd A) f)
  --   --   → η-pos (IdMnd A) τ ↦ η-posᵢ A τ
  --   -- {-# REWRITE η-pos-IdMnd #-}
    
  --   -- η-pos-elim-IdMnd : (A : Set) {f : Frm (IdMnd A)}
  --   --   → (τ : Cell (IdMnd A) f)
  --   --   → (X : (p : Pos (IdMnd A) (η (IdMnd A) τ)) → Set)
  --   --   → (η-pos* : X (η-pos (IdMnd A) τ))
  --   --   → (p : Pos (IdMnd A) (η (IdMnd A) τ))
  --   --   → η-pos-elim (IdMnd A) τ X η-pos* p ↦ η-pos-elimᵢ A τ X η-pos* p
  --   -- {-# REWRITE η-pos-elim-IdMnd #-}

  --   μ-IdMnd : (A : Set) {f : Frm (IdMnd A)} (σ : Tree (IdMnd A) f)
  --     → (δ : (p : Pos (IdMnd A) σ) → Tree (IdMnd A) (Typ (IdMnd A) σ p))
  --     → μ (IdMnd A) σ δ ↦ μᵢ A σ δ
  --   {-# REWRITE μ-IdMnd #-}
    
  --   -- μ-pos-IdMnd : (A : Set) {f : Frm (IdMnd A)} (σ : Tree (IdMnd A) f)
  --   --   → (δ : (p : Pos (IdMnd A) σ) → Tree (IdMnd A) (Typ (IdMnd A) σ p))
  --   --   → (p : Pos (IdMnd A) σ) (q : Pos (IdMnd A) (δ p))
  --   --   → μ-pos (IdMnd A) σ δ p q ↦ μ-posᵢ A σ δ p q
  --   -- {-# REWRITE μ-pos-IdMnd #-}

  --   -- μ-pos-fst-IdMnd : (A : Set) {f : Frm (IdMnd A)} (σ : Tree (IdMnd A) f)
  --   --   → (δ : (p : Pos (IdMnd A) σ) → Tree (IdMnd A) (Typ (IdMnd A) σ p))
  --   --   → (p : Pos (IdMnd A) (μ (IdMnd A) σ δ))
  --   --   → μ-pos-fst (IdMnd A) σ δ p ↦ μ-pos-fstᵢ A σ δ p
  --   -- {-# REWRITE μ-pos-fst-IdMnd #-}

  --   -- μ-pos-snd-IdMnd : (A : Set) {f : Frm (IdMnd A)} (σ : Tree (IdMnd A) f)
  --   --   → (δ : (p : Pos (IdMnd A) σ) → Tree (IdMnd A) (Typ (IdMnd A) σ p))
  --   --   → (p : Pos (IdMnd A) (μ (IdMnd A) σ δ))
  --   --   → μ-pos-snd (IdMnd A) σ δ p ↦ μ-pos-sndᵢ A σ δ p
  --   -- {-# REWRITE μ-pos-snd-IdMnd #-}

  𝕆Mnd : (n : ℕ) → 𝕄
  𝕆Mnd O = IdMnd ⊤
  𝕆Mnd (S n) = Slice (𝕆Mnd n)

  𝕆 : (n : ℕ) → Set
  𝕆 n = Frm (𝕆Mnd n) 
