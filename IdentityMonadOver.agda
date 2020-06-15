{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver 
open import IdentityMonad

module IdentityMonadOver (A : Set) where

  Idx↓ᵢ : Idxᵢ → Set
  Idx↓ᵢ ttᵢ = A

  Cns↓ᵢ : {u : Idxᵢ} (a : Idx↓ᵢ u)
    → Cnsᵢ u → Set
  Cns↓ᵢ {ttᵢ} a ttᵢ = ⊤ᵢ 

  Typ↓ᵢ : {u : Idxᵢ} {c : Cnsᵢ u}
    → {a : Idx↓ᵢ u} (d : Cns↓ᵢ a c)
    → (p : Posᵢ c) → Idx↓ᵢ (Typᵢ c p)
  Typ↓ᵢ {ttᵢ} {ttᵢ} {a} ttᵢ ttᵢ = a 

  η↓ᵢ : {u : Idxᵢ} (a : Idx↓ᵢ u)
    → Cns↓ᵢ a (ηᵢ u)
  η↓ᵢ {ttᵢ} a = ttᵢ

  μ↓ᵢ : {u : Idxᵢ} {c : Cnsᵢ u}
    → {δ : (p : Posᵢ c) → Cnsᵢ (Typᵢ c p)}
    → {a : Idx↓ᵢ u} (d : Cns↓ᵢ a c)
    → (δ↓ : (p : Posᵢ c) → Cns↓ᵢ (Typ↓ᵢ {a = a} d p) (δ p))
    → Cns↓ᵢ a (μᵢ c δ)
  μ↓ᵢ {ttᵢ} {ttᵢ} {δ} {a} d δ↓ = δ↓ ttᵢ

  postulate

    IdMnd↓ : 𝕄↓ IdMnd

    Idx↓-IdMnd↓ : (u : Idxᵢ)
      → Idx↓ IdMnd↓ u ↦ Idx↓ᵢ u
    {-# REWRITE Idx↓-IdMnd↓ #-}

    Cns↓-IdMnd↓ : {u : Idxᵢ} (a : Idx↓ᵢ u) (c : Cnsᵢ u)
      → Cns↓ IdMnd↓ a c ↦ Cns↓ᵢ a c
    {-# REWRITE Cns↓-IdMnd↓ #-}

    Typ↓-IdMnd↓ : {u : Idxᵢ} {c : Cnsᵢ u}
      → {a : Idx↓ᵢ u} (d : Cns↓ᵢ a c)
      → (p : Posᵢ c)
      → Typ↓ IdMnd↓ {f↓ = a} d p ↦ Typ↓ᵢ {a = a} d p
    {-# REWRITE Typ↓-IdMnd↓ #-} 

    η↓-IdMnd↓ : {u : Idxᵢ} (a : Idx↓ᵢ u)
      → η↓ IdMnd↓ a ↦ η↓ᵢ a
    {-# REWRITE η↓-IdMnd↓ #-}

    μ↓-IdMnd↓ : {u : Idxᵢ} {c : Cnsᵢ u}
      → {δ : (p : Posᵢ c) → Cnsᵢ (Typᵢ c p)}
      → {a : Idx↓ᵢ u} (d : Cns↓ᵢ a c)
      → (δ↓ : (p : Posᵢ c) → Cns↓ᵢ (Typ↓ᵢ {a = a} d p) (δ p))
      → μ↓ IdMnd↓ {f↓ = a} d δ↓ ↦ μ↓ᵢ {a = a} d δ↓ 
    {-# REWRITE μ↓-IdMnd↓ #-} 
