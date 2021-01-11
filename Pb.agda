{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad

module Pb where

  postulate

    Pb : (M : 𝕄) (X : Idx M → Set) → 𝕄

    Idx-Pb : (M : 𝕄) (X : Idx M → Set)
      → Idx (Pb M X) ↦ Σ (Idx M) X
    {-# REWRITE Idx-Pb #-}

    -- Idxₚ : (M : 𝕄) (X : Idx M → Set) → Set
    -- Idxₚ M X = Σ (Idx M) X

    Cns-Pb : (M : 𝕄) (X : Idx M → Set)
      → (i : Idx M) (x : X i)
      → Cns (Pb M X) (i , x) ↦ Σ (Cns M i) (λ c → (p : Pos M c) → X (Typ M c p))
    {-# REWRITE Cns-Pb #-}

    -- Cnsₚ : (M : 𝕄) (X : Idx M → Set) (i : Idxₚ M X) → Set
    -- Cnsₚ M X (i , x) = Σ (Cns M i) (λ c → (p : Pos M c) → X (Typ M c p))

    Pos-Pb : (M : 𝕄) (X : Idx M → Set)
      → {i : Idx M} {x : X i}
      → (c : Cns M i) (ν : (p : Pos M c) → X (Typ M c p))
      → Pos (Pb M X) {i = (i , x)} (c , ν) ↦ Pos M c
    {-# REWRITE Pos-Pb #-}

    -- Posₚ : (M : 𝕄) (X : Idx M → Set) {i : Idxₚ M X}
    --   → Cnsₚ M X i → Set
    -- Posₚ M X (c , ν) = Pos M c

    Typ-Pb : (M : 𝕄) (X : Idx M → Set)
      → {i : Idx M} {x : X i}
      → (c : Cns M i) (ν : (p : Pos M c) → X (Typ M c p))
      → (p : Pos (Pb M X) {i = i , x} (c , ν))
      → Typ (Pb M X) {i = i , x} (c , ν) p ↦ Typ M c p , ν p 
    {-# REWRITE Typ-Pb #-}
    
    -- Typₚ : (M : 𝕄) (X : Idx M → Set) {i : Idxₚ M X}
    --   → (c : Cnsₚ M X i) (p : Posₚ M X {i = i} c)
    --   → Idxₚ M X 
    -- Typₚ M X {i = i , x} (c , ν) p = Typ M c p , ν p

    η-Pb : (M : 𝕄) (X : Idx M → Set) 
      → (i : Idx M) (x : X i) 
      → η (Pb M X) (i , x) ↦ η M i , cst x
    {-# REWRITE η-Pb #-}

    -- ηₚ : (M : 𝕄) (X : Idx M → Set) (i : Idxₚ M X)
    --   → Cnsₚ M X i
    -- ηₚ M X (i , x) = η M i , λ _ → x

    η-pos-Pb : (M : 𝕄) (X : Idx M → Set) 
      → (i : Idx M) (x : X i) 
      → η-pos (Pb M X) (i , x) ↦ η-pos M i 
    {-# REWRITE η-pos-Pb #-}

    -- η-posₚ : (M : 𝕄) (X : Idx M → Set) (i : Idxₚ M X)
    --   → Posₚ M X {i = i} (ηₚ M X i)
    -- η-posₚ M X (i , x) = η-pos M i

    η-pos-elim-Pb : (M : 𝕄) (X : Idx M → Set) 
      → (i : Idx M) (x : X i) 
      → (P : (p : Pos (Pb M X) {i = i , x} (η (Pb M X) (i , x))) → Set)
      → (η-pos* : P (η-pos (Pb M X) (i , x)))
      → (p : Pos (Pb M X) {i = i , x} (η (Pb M X) (i , x)))
      → η-pos-elim (Pb M X) (i , x) P η-pos* p ↦ η-pos-elim M i P η-pos* p 
    {-# REWRITE η-pos-elim-Pb #-}

    -- η-pos-elimₚ : (M : 𝕄) (X : Idx M → Set) (i : Idxₚ M X)
    --   → (P : (p : Posₚ M X {i = i} (ηₚ M X i)) → Set)
    --   → (η-pos* : P (η-posₚ M X i))
    --   → (p : Posₚ M X {i = i} (ηₚ M X i)) → P p
    -- η-pos-elimₚ M X (i , x) P η-pos* p = η-pos-elim M i P η-pos* p 

    μ-Pb : (M : 𝕄) (X : Idx M → Set)
      → (i : Idx M) (x : X i)
      → (c : Cns M i) (ν : (p : Pos M c) → X (Typ M c p))
      → (δ : (p : Pos M c) → Cns (Pb M X) (Typ M c p , ν p))
      → μ (Pb M X) {i = i , x} (c , ν) δ ↦
        μ M c (fst ∘ δ) , λ p → snd (δ (μ-pos-fst M c (fst ∘ δ) p)) (μ-pos-snd M c (fst ∘ δ) p)
    {-# REWRITE μ-Pb #-}
    
    -- μₚ : (M : 𝕄) (X : Idx M → Set)
    --   → {i : Idxₚ M X} (c : Cnsₚ M X i)
    --   → (δ : (p : Posₚ M X {i = i} c) → Cnsₚ M X (Typₚ M X {i = i} c p))
    --   → Cnsₚ M X i
    -- μₚ M X {i = i , x} (c , ν) κ =
    --   let κ' p = fst (κ p)
    --       ν' p = snd (κ (μ-pos-fst M c κ' p)) (μ-pos-snd M c κ' p)
    --   in μ M c κ' , ν'

    μ-pos-Pb : (M : 𝕄) (X : Idx M → Set) 
      → (i : Idx M) (x : X i)
      → (c : Cns M i) (ν : (p : Pos M c) → X (Typ M c p))
      → (δ : (p : Pos M c) → Cns (Pb M X) (Typ M c p , ν p))
      → (p : Pos M c) (q : Pos M (fst (δ p)))
      → μ-pos (Pb M X) {i = i , x} (c , ν) δ p q ↦ μ-pos M c (fst ∘ δ) p q 
    {-# REWRITE μ-pos-Pb #-}

    -- μ-posₚ : (M : 𝕄) (X : Idx M → Set)
    --   → {i : Idxₚ M X} (c : Cnsₚ M X i)
    --   → (δ : (p : Posₚ M X {i = i} c) → Cnsₚ M X (Typₚ M X {i = i} c p))
    --   → (p : Posₚ M X {i = i} c) (q : Posₚ M X {i = Typₚ M X {i = i} c p} (δ p))
    --   → Posₚ M X {i = i} (μₚ M X {i = i} c δ)
    -- μ-posₚ M X {i = i , x} (c , ν) δ p q = μ-pos M c (fst ∘ δ) p q

    μ-pos-fst-Pb : (M : 𝕄) (X : Idx M → Set) 
      → (i : Idx M) (x : X i)
      → (c : Cns M i) (ν : (p : Pos M c) → X (Typ M c p))
      → (δ : (p : Pos M c) → Cns (Pb M X) (Typ M c p , ν p))
      → (p : Pos (Pb M X) {i = i , x} (μ (Pb M X) {i = i , x} (c , ν) δ))
      → μ-pos-fst (Pb M X) {i = i , x} (c , ν) δ p ↦ μ-pos-fst M c (fst ∘ δ) p
    {-# REWRITE μ-pos-fst-Pb #-}
    
    -- μ-pos-fstₚ : (M : 𝕄) (X : Idx M → Set)
    --   → {i : Idxₚ M X} (c : Cnsₚ M X i)
    --   → (δ : (p : Posₚ M X {i = i} c) → Cnsₚ M X (Typₚ M X {i = i} c p))
    --   → Posₚ M X {i = i} (μₚ M X {i = i} c δ) → Posₚ M X {i = i} c
    -- μ-pos-fstₚ M X {i = i , x} (c , ν) δ p = μ-pos-fst M c (fst ∘ δ) p

    μ-pos-snd-Pb : (M : 𝕄) (X : Idx M → Set) 
      → (i : Idx M) (x : X i)
      → (c : Cns M i) (ν : (p : Pos M c) → X (Typ M c p))
      → (δ : (p : Pos M c) → Cns (Pb M X) (Typ M c p , ν p))
      → (p : Pos (Pb M X) {i = i , x} (μ (Pb M X) {i = i , x} (c , ν) δ))
      → μ-pos-snd (Pb M X) {i = i , x} (c , ν) δ p ↦ μ-pos-snd M c (fst ∘ δ) p
    {-# REWRITE μ-pos-snd-Pb #-}

    -- μ-pos-sndₚ : (M : 𝕄) (X : Idx M → Set)
    --   → {i : Idxₚ M X} (c : Cnsₚ M X i)
    --   → (δ : (p : Posₚ M X {i = i} c) → Cnsₚ M X (Typₚ M X {i = i} c p))
    --   → (p : Posₚ M X {i = i} (μₚ M X {i = i} c δ))
    --   → Posₚ M X {i = Typₚ M X {i = i} c (μ-pos-fstₚ M X {i = i} c δ p)} (δ (μ-pos-fstₚ M X {i = i} c δ p))
    -- μ-pos-sndₚ M X {i = i , x} (c , ν) δ p = μ-pos-snd M c (fst ∘ δ) p

