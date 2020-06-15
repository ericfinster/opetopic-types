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


  -- Yeah, it's messy, but this looks like a solution.
  -- data InnerFace : {n : ℕ} → 𝕆 n → ℕ → 𝕌 where
  --   src-face : {n : ℕ} (o : 𝕆 n) (p : ℙ o) (q : ℙ (o ▸ p)) (u : Pos q) → InnerFace (o ▸ p ▸ q) (S n)
  --   tgt-face : {n : ℕ} (o : 𝕆 n) (p : ℙ o) (q : ℙ (o ▸ p)) (u : Pos q) → InnerFace (o ▸ p ▸ q) n
  --   raise-face : {n m : ℕ} (o : 𝕆 n) (p : ℙ o) → InnerFace o m → InnerFace (o ▸ p) m

  -- data Face : {n : ℕ} → 𝕆 n → ℕ → 𝕌 where
  --   top : {n : ℕ} (o : 𝕆 n) → Face o n
  --   tgt : {n : ℕ} (o : 𝕆 (S n)) → Face o n
  --   init : {n : ℕ} (o : 𝕆 (S n)) → Face o 0
  --   inner : {n m : ℕ} (o : 𝕆 n) → InnerFace o m → Face o m
    
  -- ob-face : Face ● 0
  -- ob-face = top ●

  -- arr-src-face : Face arrow 0
  -- arr-src-face = init (● ▸ arr)

  -- arr-tgt-face : Face arrow 0
  -- arr-tgt-face = tgt (● ▸ arr)

  -- drop-obj-face : Face 2-drop 0
  -- drop-obj-face = init _

  -- drop-arr-face : Face 2-drop 1
  -- drop-arr-face = tgt _

  -- simplex-obj-face : Face 2-simplex 0
  -- simplex-obj-face = inner _ (tgt-face ● arr _ (nd-pos-here ● arr _ _))
