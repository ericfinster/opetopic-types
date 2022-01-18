{-# OPTIONS --without-K --rewriting #-}

open import MiniHoTT

open import Opetopes

module Faces where

  data InnerFace : {n : ℕ} → 𝒪 n → ℕ → Set where
    src-face : {n : ℕ} (o : 𝒪 n) (p : 𝒫 o) (q : 𝒫 (o , p))
      → Pos q → InnerFace ((o , p) , q) (S n)
    tgt-face : {n : ℕ} (o : 𝒪 n) (p : 𝒫 o) (q : 𝒫 (o , p))
      → Pos q → InnerFace ((o , p) , q) n
    raise-face : {n m : ℕ} (o : 𝒪 n) (p : 𝒫 o)
      → InnerFace o m → InnerFace (o , p) m 

  data Face : {n : ℕ} → 𝒪 n → ℕ → Set where
    top : {n : ℕ} (o : 𝒪 n) → Face o n
    tgt : {n : ℕ} (o : 𝒪 (S n)) → Face o n
    init : {n : ℕ} (o : 𝒪 (S n)) → Face o 0
    inner : {n m : ℕ} (o : 𝒪 n) → InnerFace o m → Face o m  

  -- obj : 𝒪 0
  -- obj = tt

  obj-face : Face obj 0 
  obj-face = top tt
  
  -- arrow : 𝒪 1
  -- arrow = tt , tt

  arrow-src : Face arrow 0
  arrow-src = init arrow
  
  arrow-tgt : Face arrow 0
  arrow-tgt = tgt arrow 

  arrow-top : Face arrow 1
  arrow-top = top arrow

  -- 2-simplex : 𝒪 2
  -- 2-simplex = (tt , tt) , ndₒ tt tt (cst tt) (λ p → ndₒ tt tt (cst tt) (cst (lfₒ tt)))
  
  simplex = 2-simplex

  simp-init : Face simplex 0
  simp-init = init simplex 

  simp-mid : Face simplex 0
  simp-mid = inner simplex (tgt-face tt tt
                              (ndₒ tt tt (cst tt) (λ p → ndₒ tt tt (cst tt) (cst (lfₒ tt)))) (inl tt))

  simp-term : Face simplex 0
  simp-term = inner simplex (tgt-face tt tt
                              (ndₒ tt tt (cst tt) (λ p → ndₒ tt tt (cst tt) (cst (lfₒ tt)))) (inr (tt , inl tt))) 

  simp-fst : Face simplex 1
  simp-fst = inner simplex (src-face tt tt
                              (ndₒ tt tt (cst tt) (λ p → ndₒ tt tt (cst tt) (cst (lfₒ tt)))) (inl tt))

  simp-snd : Face simplex 1
  simp-snd = inner simplex (src-face tt tt
                              (ndₒ tt tt (cst tt) (λ p → ndₒ tt tt (cst tt) (cst (lfₒ tt)))) (inr (tt , inl tt))) 

  simp-tgt : Face simplex 1
  simp-tgt = tgt simplex

  simp-top : Face simplex 2
  simp-top = top simplex 
