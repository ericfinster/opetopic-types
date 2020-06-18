{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver 
open import IdentityMonad

module IdentityMonadOver (A : Set) where

  Idx↓ᵢ : Idxᵢ → Set
  Idx↓ᵢ _ = A

  Cns↓ᵢ : {u : Idxᵢ} (a : Idx↓ᵢ u)
    → Cnsᵢ u → Set
  Cns↓ᵢ a _ = ⊤ᵢ 

  Typ↓ᵢ : {u : Idxᵢ} {c : Cnsᵢ u}
    → {a : Idx↓ᵢ u} (d : Cns↓ᵢ {u = u} a c)
    → (p : Posᵢ {u = u} c) → Idx↓ᵢ (Typᵢ {u = u} c p)
  Typ↓ᵢ {a = a} _ _ = a 

  η↓ᵢ : {u : Idxᵢ} (a : Idx↓ᵢ u)
    → Cns↓ᵢ {u = u} a (ηᵢ u)
  η↓ᵢ a = ttᵢ

  μ↓ᵢ : {u : Idxᵢ} {c : Cnsᵢ u}
    → {δ : (p : Posᵢ {u = u} c) → Cnsᵢ (Typᵢ {u = u} c p)}
    → {a : Idx↓ᵢ u} (d : Cns↓ᵢ {u = u} a c)
    → (δ↓ : (p : Posᵢ {u = u} c) → Cns↓ᵢ {u = u} (Typ↓ᵢ {u = u} {c = c} {a = a} d p) (δ p))
    → Cns↓ᵢ {u = u} a (μᵢ {u = u} c δ)
  μ↓ᵢ {δ = δ} {a = a} d δ↓ = δ↓ ttᵢ

  postulate

    IdMnd↓ : 𝕄↓ IdMnd

    Idx↓-IdMnd↓ : (u : Idxᵢ)
      → Idx↓ IdMnd↓ u ↦ Idx↓ᵢ u
    {-# REWRITE Idx↓-IdMnd↓ #-}

    Cns↓-IdMnd↓ : {u : Idxᵢ} (a : Idx↓ᵢ u) (c : Cnsᵢ u)
      → Cns↓ IdMnd↓ {i = u} a c ↦ Cns↓ᵢ {u = u} a c
    {-# REWRITE Cns↓-IdMnd↓ #-}

    Typ↓-IdMnd↓ : {u : Idxᵢ} {c : Cnsᵢ u}
      → {a : Idx↓ᵢ u} (d : Cns↓ᵢ {u = u} a c)
      → (p : Posᵢ {u = u} c)
      → Typ↓ IdMnd↓ {i = u} {c = c} {i↓ = a} d p ↦ Typ↓ᵢ {u = u} {c = c} {a = a} d p
    {-# REWRITE Typ↓-IdMnd↓ #-} 

    η↓-IdMnd↓ : {u : Idxᵢ} (a : Idx↓ᵢ u)
      → η↓ IdMnd↓ {i = u} a ↦ η↓ᵢ {u = u} a
    {-# REWRITE η↓-IdMnd↓ #-}

    μ↓-IdMnd↓ : {u : Idxᵢ} {c : Cnsᵢ u}
      → {δ : (p : Posᵢ {u = u} c) → Cnsᵢ (Typᵢ {u = u} c p)}
      → {a : Idx↓ᵢ u} (d : Cns↓ᵢ {u = u} a c)
      → (δ↓ : (p : Posᵢ {u = u} c) → Cns↓ᵢ {u = u} (Typ↓ᵢ {u = u} {c = c} {a = a} d p) (δ p))
      → μ↓ IdMnd↓ {i = u} {c = c} {δ = δ} {i↓ = a} d δ↓ ↦ μ↓ᵢ {u = u} {c = c} {δ = δ} {a = a} d δ↓ 
    {-# REWRITE μ↓-IdMnd↓ #-}
