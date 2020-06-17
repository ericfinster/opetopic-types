{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad

module Pb where

  Idxₚ : (M : 𝕄) (X : Idx M → Set) → Set
  Idxₚ M X = Σ (Idx M) X

  Cnsₚ : (M : 𝕄) (X : Idx M → Set) (i : Idxₚ M X) → Set
  Cnsₚ M X (i , x) = Σ (Cns M i) (λ c → (p : Pos M c) → X (Typ M c p))
  
  Posₚ : (M : 𝕄) (X : Idx M → Set) {i : Idxₚ M X}
    → Cnsₚ M X i → Set
  Posₚ M X (c , ν) = Pos M c
  
  Typₚ : (M : 𝕄) (X : Idx M → Set) {i : Idxₚ M X}
    → (c : Cnsₚ M X i) (p : Posₚ M X {i = i} c)
    → Idxₚ M X 
  Typₚ M X {i = i , x} (c , ν) p = Typ M c p , ν p

  ηₚ : (M : 𝕄) (X : Idx M → Set) (i : Idxₚ M X)
    → Cnsₚ M X i
  ηₚ M X (i , x) = η M i , λ _ → x

  η-posₚ : (M : 𝕄) (X : Idx M → Set) (i : Idxₚ M X)
    → Posₚ M X {i = i} (ηₚ M X i)
  η-posₚ M X (i , x) = η-pos M i

  η-pos-elimₚ : (M : 𝕄) (X : Idx M → Set) (i : Idxₚ M X)
    → (P : (p : Posₚ M X {i = i} (ηₚ M X i)) → Set)
    → (η-pos* : P (η-posₚ M X i))
    → (p : Posₚ M X {i = i} (ηₚ M X i)) → P p
  η-pos-elimₚ M X (i , x) P η-pos* p = η-pos-elim M i P η-pos* p 

  μₚ : (M : 𝕄) (X : Idx M → Set)
    → {i : Idxₚ M X} (c : Cnsₚ M X i)
    → (δ : (p : Posₚ M X {i = i} c) → Cnsₚ M X (Typₚ M X {i = i} c p))
    → Cnsₚ M X i
  μₚ M X {i = i , x} (c , ν) κ =
    let κ' p = fst (κ p)
        ν' p = snd (κ (μ-pos-fst M c κ' p)) (μ-pos-snd M c κ' p)
    in μ M c κ' , ν'

  μ-posₚ : (M : 𝕄) (X : Idx M → Set)
    → {i : Idxₚ M X} (c : Cnsₚ M X i)
    → (δ : (p : Posₚ M X {i = i} c) → Cnsₚ M X (Typₚ M X {i = i} c p))
    → (p : Posₚ M X {i = i} c) (q : Posₚ M X {i = Typₚ M X {i = i} c p} (δ p))
    → Posₚ M X {i = i} (μₚ M X {i = i} c δ)
  μ-posₚ M X {i = i , x} (c , ν) δ p q = μ-pos M c (fst ∘ δ) p q

  μ-pos-fstₚ : (M : 𝕄) (X : Idx M → Set)
    → {i : Idxₚ M X} (c : Cnsₚ M X i)
    → (δ : (p : Posₚ M X {i = i} c) → Cnsₚ M X (Typₚ M X {i = i} c p))
    → Posₚ M X {i = i} (μₚ M X {i = i} c δ) → Posₚ M X {i = i} c
  μ-pos-fstₚ M X {i = i , x} (c , ν) δ p = μ-pos-fst M c (fst ∘ δ) p

  μ-pos-sndₚ : (M : 𝕄) (X : Idx M → Set)
    → {i : Idxₚ M X} (c : Cnsₚ M X i)
    → (δ : (p : Posₚ M X {i = i} c) → Cnsₚ M X (Typₚ M X {i = i} c p))
    → (p : Posₚ M X {i = i} (μₚ M X {i = i} c δ))
    → Posₚ M X {i = Typₚ M X {i = i} c (μ-pos-fstₚ M X {i = i} c δ p)} (δ (μ-pos-fstₚ M X {i = i} c δ p))
  μ-pos-sndₚ M X {i = i , x} (c , ν) δ p = μ-pos-snd M c (fst ∘ δ) p
  
  postulate

    Pb : (M : 𝕄) (X : Idx M → Set) → 𝕄

    Idx-Pb : (M : 𝕄) (X : Idx M → Set)
      → Idx (Pb M X) ↦ Idxₚ M X
    {-# REWRITE Idx-Pb #-}
    
    Cns-Pb : (M : 𝕄) (X : Idx M → Set) 
      → Cns (Pb M X) ↦ Cnsₚ M X 
    {-# REWRITE Cns-Pb #-}

    Pos-Pb : (M : 𝕄) (X : Idx M → Set) 
      → {i : Idx (Pb M X)}
      → (c : Cns (Pb M X) i)
      → Pos (Pb M X) {i = i} c ↦ Posₚ M X {i = i} c
    {-# REWRITE Pos-Pb #-}

    Typ-Pb : (M : 𝕄) (X : Idx M → Set) 
      → {i : Idx (Pb M X)}
      → (c : Cns (Pb M X) i) (p : Pos (Pb M X) {i = i} c)
      → Typ (Pb M X) {i = i} c p ↦ Typₚ M X {i = i} c p
    {-# REWRITE Typ-Pb #-}

    η-Pb : (M : 𝕄) (X : Idx M → Set) 
      → (i : Idx (Pb M X))
      → η (Pb M X) i ↦ ηₚ M X i
    {-# REWRITE η-Pb #-}

    η-pos-Pb : (M : 𝕄) (X : Idx M → Set) 
      → (i : Idx (Pb M X))
      → η-pos (Pb M X) i ↦ η-posₚ M X i
    {-# REWRITE η-pos-Pb #-}

    η-pos-elim-Pb : (M : 𝕄) (X : Idx M → Set) 
      → (i : Idx (Pb M X))
      → (P : (p : Pos (Pb M X) {i = i} (η (Pb M X) i)) → Set)
      → (η-pos* : P (η-pos (Pb M X) i))
      → (p : Pos (Pb M X) {i = i} (η (Pb M X) i))
      → η-pos-elim (Pb M X) i P η-pos* p ↦ η-pos-elimₚ M X i P η-pos* p 
    {-# REWRITE η-pos-elim-Pb #-}

    μ-Pb : (M : 𝕄) (X : Idx M → Set) 
      → {i : Idx (Pb M X)} (c : Cns (Pb M X) i)
      → (δ : (p : Pos (Pb M X) {i = i} c) → Cns (Pb M X) (Typ (Pb M X) {i = i} c p))
      → μ (Pb M X) {i = i} c δ ↦ μₚ M X {i = i} c δ
    {-# REWRITE μ-Pb #-}

    μ-pos-Pb : (M : 𝕄) (X : Idx M → Set) 
      → {i : Idx (Pb M X)} (c : Cns (Pb M X) i)
      → (δ : (p : Pos (Pb M X) {i = i} c) → Cns (Pb M X) (Typ (Pb M X) {i = i} c p))
      → (p : Pos (Pb M X) {i = i} c) (q : Pos (Pb M X) {i = Typₚ M X {i = i} c p} (δ p))
      → μ-pos (Pb M X) {i = i} c δ p q ↦ μ-posₚ M X {i = i} c δ p q
    {-# REWRITE μ-pos-Pb #-}

    μ-pos-fst-Pb : (M : 𝕄) (X : Idx M → Set) 
      → {i : Idx (Pb M X)} (c : Cns (Pb M X) i)
      → (δ : (p : Pos (Pb M X) {i = i} c) → Cns (Pb M X) (Typ (Pb M X) {i = i} c p))
      → (p : Pos (Pb M X) {i = i} (μ (Pb M X) {i = i} c δ))
      → μ-pos-fst (Pb M X) {i = i} c δ p ↦ μ-pos-fstₚ M X {i = i} c δ p
    {-# REWRITE μ-pos-fst-Pb #-}
    
    μ-pos-snd-Pb : (M : 𝕄) (X : Idx M → Set) 
      → {i : Idx (Pb M X)} (c : Cns (Pb M X) i)
      → (δ : (p : Pos (Pb M X) {i = i} c) → Cns (Pb M X) (Typ (Pb M X) {i = i} c p))
      → (p : Pos (Pb M X) {i = i} (μ (Pb M X) {i = i} c δ))
      → μ-pos-snd (Pb M X) {i = i} c δ p ↦ μ-pos-sndₚ M X {i = i} c δ p
    {-# REWRITE μ-pos-snd-Pb #-}


