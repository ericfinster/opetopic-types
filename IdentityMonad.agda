{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad

module IdentityMonad where

  data ⊤ᵢ : Set where
    ttᵢ : ⊤ᵢ

  Idxᵢ : Set
  Idxᵢ = ⊤ᵢ

  Cnsᵢ : Idxᵢ → Set
  Cnsᵢ ttᵢ = ⊤ᵢ

  Posᵢ : {u : Idxᵢ} → Cnsᵢ u → Set
  Posᵢ {ttᵢ} ttᵢ = ⊤ᵢ

  Typᵢ : {u : Idxᵢ} (c : Cnsᵢ u) → Posᵢ c → ⊤ᵢ
  Typᵢ {ttᵢ} ttᵢ ttᵢ = ttᵢ

  ηᵢ : (u : Idxᵢ) → Cnsᵢ u
  ηᵢ ttᵢ = ttᵢ

  η-posᵢ : (u : Idxᵢ) → Posᵢ (ηᵢ u)
  η-posᵢ ttᵢ = ttᵢ
  
  η-pos-elimᵢ : (u : Idxᵢ)
    → (X : (p : Posᵢ (ηᵢ u)) → Set)
    → (η-pos* : X (η-posᵢ u))
    → (p : Posᵢ (ηᵢ u)) → X p
  η-pos-elimᵢ ttᵢ X η-pos* ttᵢ = η-pos*
  
  μᵢ : {u : Idxᵢ} (c : Cnsᵢ u)
    → (δ : (p : Posᵢ c) → Cnsᵢ (Typᵢ c p))
    → Cnsᵢ u
  μᵢ {ttᵢ} ttᵢ δ = δ ttᵢ 

  μ-posᵢ : {u : Idxᵢ} (c : Cnsᵢ u)
    → (δ : (p : Posᵢ c) → Cnsᵢ (Typᵢ c p))
    → (p : Posᵢ c) (q : Posᵢ (δ p))
    → Posᵢ (μᵢ c δ)
  μ-posᵢ {ttᵢ} ttᵢ δ ttᵢ q = q

  μ-pos-fstᵢ : {u : Idxᵢ} (c : Cnsᵢ u)
    → (δ : (p : Posᵢ c) → Cnsᵢ (Typᵢ c p))
    → (p : Posᵢ (μᵢ c δ)) → Posᵢ c
  μ-pos-fstᵢ {ttᵢ} ttᵢ δ p = ttᵢ

  μ-pos-sndᵢ : {u : Idxᵢ} (c : Cnsᵢ u)
    → (δ : (p : Posᵢ c) → Cnsᵢ (Typᵢ c p))
    → (p : Posᵢ (μᵢ c δ))
    → Posᵢ (δ (μ-pos-fstᵢ c δ p))
  μ-pos-sndᵢ {ttᵢ} ttᵢ δ p = p 

  postulate

    IdMnd : 𝕄

    Idx-IdMnd : Idx IdMnd ↦ Idxᵢ 
    {-# REWRITE Idx-IdMnd #-}

    Cns-IdMnd : (u : Idxᵢ)
      → Cns IdMnd u ↦ Cnsᵢ u
    {-# REWRITE Cns-IdMnd #-}

    Pos-IdMnd : (u : Idxᵢ) (c : Cnsᵢ u)
      → Pos IdMnd c ↦ Posᵢ c
    {-# REWRITE Pos-IdMnd #-}

    Typ-IdMnd : (u : Idxᵢ) (c : Cnsᵢ u) (p : Posᵢ c)
      → Typ IdMnd c p ↦ Typᵢ c p
    {-# REWRITE Typ-IdMnd #-}

    η-IdMnd : (u : Idxᵢ) 
      → η IdMnd u ↦ ηᵢ u
    {-# REWRITE η-IdMnd #-}

    η-pos-IdMnd : (u : Idxᵢ)
      → η-pos IdMnd u ↦ η-posᵢ u
    {-# REWRITE η-pos-IdMnd #-}

    η-pos-elim-IdMnd : (u : Idxᵢ)
      → (X : (p : Posᵢ (ηᵢ u)) → Set)
      → (η-pos* : X (η-posᵢ u))
      → (p : Posᵢ (ηᵢ u)) → X p
      → η-pos-elim IdMnd u X η-pos* p ↦ η-pos-elimᵢ u X η-pos* p
    {-# REWRITE η-pos-elim-IdMnd #-}
    
    μ-IdMnd : {u : Idxᵢ} (c : Cnsᵢ u)
      → (δ : (p : Posᵢ c) → Cnsᵢ (Typᵢ c p))
      → μ IdMnd c δ ↦ μᵢ c δ
    {-# REWRITE μ-IdMnd #-}

    μ-pos-IdMnd : {u : Idxᵢ} (c : Cnsᵢ u)
      → (δ : (p : Posᵢ c) → Cnsᵢ (Typᵢ c p))
      → (p : Posᵢ c) (q : Posᵢ (δ p))
      → μ-pos IdMnd c δ p ↦ μ-posᵢ c δ p
    {-# REWRITE μ-pos-IdMnd #-}

    μ-pos-fst-IdMnd : {u : Idxᵢ} (c : Cnsᵢ u)
      → (δ : (p : Posᵢ c) → Cnsᵢ (Typᵢ c p))
      → (p : Posᵢ (μᵢ c δ)) 
      → μ-pos-fst IdMnd c δ p ↦ μ-pos-fstᵢ c δ p
    {-# REWRITE μ-pos-fst-IdMnd #-}

    μ-pos-snd-IdMnd : {u : Idxᵢ} (c : Cnsᵢ u)
      → (δ : (p : Posᵢ c) → Cnsᵢ (Typᵢ c p))
      → (p : Posᵢ (μᵢ c δ))
      → μ-pos-snd IdMnd c δ p ↦ μ-pos-sndᵢ c δ p
    {-# REWRITE μ-pos-snd-IdMnd #-} 



