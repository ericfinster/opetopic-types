{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import IdentityMonad

module Opetopes where

  𝕆Mnd : ℕ → 𝕄 
  𝕆Mnd O = IdMnd
  𝕆Mnd (S n) = Slice (𝕆Mnd n)

  𝕆 : ℕ → Set
  𝕆 n = Idx (𝕆Mnd n)

  --
  --  Examples
  --
  
  obj : 𝕆 0
  obj = ttᵢ

  arr : 𝕆 1
  arr = ttᵢ , ttᵢ 

  drop₂ : 𝕆 2
  drop₂ = (ttᵢ , ttᵢ) , lf ttᵢ

  glob₂ : 𝕆 2
  glob₂ = (ttᵢ , ttᵢ) , (nd ttᵢ (λ { ttᵢ → ttᵢ })
                                (λ { ttᵢ → lf ttᵢ }))

  -- Attempt at the representable ...

  data InnerFace : {n : ℕ} → 𝕆 n → ℕ → Set where
    src-face : {n : ℕ} (o : 𝕆 n) (p : Cns (𝕆Mnd n) o) (q : Cns (𝕆Mnd (S n)) (o , p))
      → InnerFace {S (S n)} ((o , p) , q) (S n)
    tgt-face : {n : ℕ} (o : 𝕆 n) (p : Cns (𝕆Mnd n) o) (q : Cns (𝕆Mnd (S n)) (o , p))
      → InnerFace {S (S n)} ((o , p) , q) n
    raise-face : {n m : ℕ} (o : 𝕆 n) (p : Cns (𝕆Mnd n) o)
      → InnerFace {n} o m → InnerFace {S n} (o , p) m 

  data Face : (n : ℕ) → 𝕆 n → ℕ → Set where
    top : {n : ℕ} (o : 𝕆 n) → Face n o n
    tgt : {n : ℕ} (o : 𝕆 (S n)) → Face (S n) o n
    init : {n : ℕ} (o : 𝕆 (S n)) → Face (S n) o 0
    inner : {n m : ℕ} (o : 𝕆 n) → InnerFace {n} o m → Face n o m  
    
  --
  --  Example faces
  --

  obj-face : Face 0 obj 0
  obj-face = top obj

  arr-src-face : Face 1 arr 0
  arr-src-face = init arr

  arr-tgt-face : Face 1 arr 0
  arr-tgt-face = tgt arr

  arr-top-face : Face 1 arr 1
  arr-top-face = top arr 
