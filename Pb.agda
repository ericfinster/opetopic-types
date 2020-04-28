{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad

module Pb where

  Frmₚ : (M : 𝕄) (X : Frm M → Set) → Set
  Frmₚ M X = Σ (Frm M) X

  Treeₚ : (M : 𝕄) (X : Frm M → Set) (f : Frmₚ M X) → Set
  Treeₚ M X (f , x) = Σ (Tree M f) (λ σ → (p : Pos M σ) → X (Typ M σ p))
  
  Posₚ : (M : 𝕄) (X : Frm M → Set) {f : Frmₚ M X}
    → Treeₚ M X f → Set
  Posₚ M X (σ , ν) = Pos M σ
  
  Typₚ : (M : 𝕄) (X : Frm M → Set) {f : Frmₚ M X}
    → (σ : Treeₚ M X f) (p : Posₚ M X {f = f} σ)
    → Frmₚ M X 
  Typₚ M X {f = f , x} (σ , ν) p = Typ M σ p , ν p

  ηₚ : (M : 𝕄) (X : Frm M → Set) (f : Frmₚ M X)
    → Treeₚ M X f
  ηₚ M X (f , x) = η M f , λ _ → x

  η-posₚ : (M : 𝕄) (X : Frm M → Set) (f : Frmₚ M X)
    → Posₚ M X {f = f} (ηₚ M X f)
  η-posₚ M X (f , x) = η-pos M f

  η-pos-elimₚ : (M : 𝕄) (X : Frm M → Set) (f : Frmₚ M X)
    → (P : (p : Posₚ M X {f = f} (ηₚ M X f)) → Set)
    → (η-pos* : P (η-posₚ M X f))
    → (p : Posₚ M X {f = f} (ηₚ M X f)) → P p
  η-pos-elimₚ M X (f , x) P η-pos* p = η-pos-elim M f P η-pos* p 

  μₚ : (M : 𝕄) (X : Frm M → Set)
    → {f : Frmₚ M X} (σ : Treeₚ M X f)
    → (δ : (p : Posₚ M X {f = f} σ) → Treeₚ M X (Typₚ M X {f = f} σ p))
    → Treeₚ M X f
  μₚ M X {f = f , x} (σ , ν) κ =
    let κ' p = fst (κ p)
        ν' p = snd (κ (μ-pos-fst M σ κ' p)) (μ-pos-snd M σ κ' p)
    in μ M σ κ' , ν'

  μ-posₚ : (M : 𝕄) (X : Frm M → Set)
    → {f : Frmₚ M X} (σ : Treeₚ M X f)
    → (δ : (p : Posₚ M X {f = f} σ) → Treeₚ M X (Typₚ M X {f = f} σ p))
    → (p : Posₚ M X {f = f} σ) (q : Posₚ M X {f = Typₚ M X {f = f} σ p} (δ p))
    → Posₚ M X {f = f} (μₚ M X {f = f} σ δ)
  μ-posₚ M X {f = f , x} (σ , ν) δ p q = μ-pos M σ (fst ∘ δ) p q

  μ-pos-fstₚ : (M : 𝕄) (X : Frm M → Set)
    → {f : Frmₚ M X} (σ : Treeₚ M X f)
    → (δ : (p : Posₚ M X {f = f} σ) → Treeₚ M X (Typₚ M X {f = f} σ p))
    → Posₚ M X {f = f} (μₚ M X {f = f} σ δ) → Posₚ M X {f = f} σ
  μ-pos-fstₚ M X {f = f , x} (σ , ν) δ p = μ-pos-fst M σ (fst ∘ δ) p

  μ-pos-sndₚ : (M : 𝕄) (X : Frm M → Set)
    → {f : Frmₚ M X} (σ : Treeₚ M X f)
    → (δ : (p : Posₚ M X {f = f} σ) → Treeₚ M X (Typₚ M X {f = f} σ p))
    → (p : Posₚ M X {f = f} (μₚ M X {f = f} σ δ))
    → Posₚ M X {f = Typₚ M X {f = f} σ (μ-pos-fstₚ M X {f = f} σ δ p)} (δ (μ-pos-fstₚ M X {f = f} σ δ p))
  μ-pos-sndₚ M X {f = f , x} (σ , ν) δ p = μ-pos-snd M σ (fst ∘ δ) p
  
  postulate

    Pb : (M : 𝕄) (X : Frm M → Set) → 𝕄

    Frm-Pb : (M : 𝕄) (X : Frm M → Set)
      → Frm (Pb M X) ↦ Frmₚ M X
    {-# REWRITE Frm-Pb #-}
    
    Tree-Pb : (M : 𝕄) (X : Frm M → Set) 
      → Tree (Pb M X) ↦ Treeₚ M X 
    {-# REWRITE Tree-Pb #-}

    Pos-Pb : (M : 𝕄) (X : Frm M → Set) 
      → {f : Frm (Pb M X)}
      → (σ : Tree (Pb M X) f)
      → Pos (Pb M X) {f = f} σ ↦ Posₚ M X {f = f} σ
    {-# REWRITE Pos-Pb #-}

    Typ-Pb : (M : 𝕄) (X : Frm M → Set) 
      → {f : Frm (Pb M X)}
      → (σ : Tree (Pb M X) f) (p : Pos (Pb M X) {f = f} σ)
      → Typ (Pb M X) {f = f} σ p ↦ Typₚ M X {f = f} σ p
    {-# REWRITE Typ-Pb #-}

    η-Pb : (M : 𝕄) (X : Frm M → Set) 
      → (f : Frm (Pb M X))
      → η (Pb M X) f ↦ ηₚ M X f
    {-# REWRITE η-Pb #-}

    η-pos-Pb : (M : 𝕄) (X : Frm M → Set) 
      → (f : Frm (Pb M X))
      → η-pos (Pb M X) f ↦ η-posₚ M X f
    {-# REWRITE η-pos-Pb #-}

    η-pos-elim-Pb : (M : 𝕄) (X : Frm M → Set) 
      → (f : Frm (Pb M X))
      → (P : (p : Pos (Pb M X) {f = f} (η (Pb M X) f)) → Set)
      → (η-pos* : P (η-pos (Pb M X) f))
      → (p : Pos (Pb M X) {f = f} (η (Pb M X) f))
      → η-pos-elim (Pb M X) f P η-pos* p ↦ η-pos-elimₚ M X f P η-pos* p 
    {-# REWRITE η-pos-elim-Pb #-}

    μ-Pb : (M : 𝕄) (X : Frm M → Set) 
      → {f : Frm (Pb M X)} (σ : Tree (Pb M X) f)
      → (δ : (p : Pos (Pb M X) {f = f} σ) → Tree (Pb M X) (Typ (Pb M X) {f = f} σ p))
      → μ (Pb M X) {f = f} σ δ ↦ μₚ M X {f = f} σ δ
    {-# REWRITE μ-Pb #-}

    μ-pos-Pb : (M : 𝕄) (X : Frm M → Set) 
      → {f : Frm (Pb M X)} (σ : Tree (Pb M X) f)
      → (δ : (p : Pos (Pb M X) {f = f} σ) → Tree (Pb M X) (Typ (Pb M X) {f = f} σ p))
      → (p : Pos (Pb M X) {f = f} σ) (q : Pos (Pb M X) {f = Typₚ M X {f = f} σ p} (δ p))
      → μ-pos (Pb M X) {f = f} σ δ p q ↦ μ-posₚ M X {f = f} σ δ p q
    {-# REWRITE μ-pos-Pb #-}

    μ-pos-fst-Pb : (M : 𝕄) (X : Frm M → Set) 
      → {f : Frm (Pb M X)} (σ : Tree (Pb M X) f)
      → (δ : (p : Pos (Pb M X) {f = f} σ) → Tree (Pb M X) (Typ (Pb M X) {f = f} σ p))
      → (p : Pos (Pb M X) {f = f} (μ (Pb M X) {f = f} σ δ))
      → μ-pos-fst (Pb M X) {f = f} σ δ p ↦ μ-pos-fstₚ M X {f = f} σ δ p
    {-# REWRITE μ-pos-fst-Pb #-}
    
    μ-pos-snd-Pb : (M : 𝕄) (X : Frm M → Set) 
      → {f : Frm (Pb M X)} (σ : Tree (Pb M X) f)
      → (δ : (p : Pos (Pb M X) {f = f} σ) → Tree (Pb M X) (Typ (Pb M X) {f = f} σ p))
      → (p : Pos (Pb M X) {f = f} (μ (Pb M X) {f = f} σ δ))
      → μ-pos-snd (Pb M X) {f = f} σ δ p ↦ μ-pos-sndₚ M X {f = f} σ δ p
    {-# REWRITE μ-pos-snd-Pb #-}


