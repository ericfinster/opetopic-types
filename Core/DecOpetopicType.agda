{-# OPTIONS --local-confluence-check #-}
--
--  OpetopicType.agda - Opetopic Types
--

open import Core.Prelude

module Core.DecOpetopicType where

  postulate

    --
    --  Opetopic Types
    --

    𝕆Type : (ℓ : Level) (n : ℕ) 
      → Type (ℓ-suc ℓ)

    --
    --  Polynomial Structure
    --
    
    Idx : (ℓ : Level) (n : ℕ) 
      → 𝕆Type ℓ n → Type ℓ 

    Cns : (ℓ : Level) (n : ℕ) 
      → (X : 𝕆Type ℓ n)
      → Idx ℓ n X → Type ℓ

    Pos : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X) (c : Cns ℓ n X i)
      → Type ℓ 

    Typ : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X) (c : Cns ℓ n X i)
      → (p : Pos ℓ n X i c) → Idx ℓ n X 

    --
    --  Monadic Structure
    --

    η : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X) → Cns ℓ n X i

    μ : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → Cns ℓ n X i 

    --
    --  Position Intro
    --

    η-pos : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X)
      → Pos ℓ n X i (η ℓ n X i)

    μ-pos : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i c) (q : Pos ℓ n X (Typ ℓ n X i c p) (δ p))
      → Pos ℓ n X i (μ ℓ n X i c δ)

    --
    --  Position Elim
    --

    η-pos-elim : (ℓ ℓ' : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X)
      → (P : Pos ℓ n X i (η ℓ n X i) → Type ℓ')
      → (η-pos* : P (η-pos ℓ n X i))
      → (p : Pos ℓ n X i (η ℓ n X i)) → P p

    μ-fst : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i (μ ℓ n X i c δ))
      → Pos ℓ n X i c
      
    μ-snd : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i (μ ℓ n X i c δ))
      → Pos ℓ n X (Typ ℓ n X i c (μ-fst ℓ n X i c δ p))
          (δ (μ-fst ℓ n X i c δ p)) 

    --
    --  Position Computation Rules
    --

    η-pos-elim-β : (ℓ ℓ' : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X)
      → (P : Pos ℓ n X i (η ℓ n X i) → Type ℓ')
      → (η-pos* : P (η-pos ℓ n X i))
      → η-pos-elim ℓ ℓ' n X i P η-pos* (η-pos ℓ n X i) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}

    μ-fst-β : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i c) (q : Pos ℓ n X (Typ ℓ n X i c p) (δ p))
      → μ-fst ℓ n X i c δ (μ-pos ℓ n X i c δ p q) ↦ p
    {-# REWRITE μ-fst-β #-}
    
    μ-snd-β : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i c) (q : Pos ℓ n X (Typ ℓ n X i c p) (δ p))
      → μ-snd ℓ n X i c δ (μ-pos ℓ n X i c δ p q) ↦ q
    {-# REWRITE μ-snd-β #-}

    μ-pos-η : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i (μ ℓ n X i c δ))
      → μ-pos ℓ n X i c δ (μ-fst ℓ n X i c δ p) (μ-snd ℓ n X i c δ p) ↦ p
    {-# REWRITE μ-pos-η #-}

    --
    --  Position Typing Rules
    --

    Typ-η : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X)
      → (p : Pos ℓ n X i (η ℓ n X i))
      → Typ ℓ n X i (η ℓ n X i) p ↦ i
    {-# REWRITE Typ-η #-}

    Typ-μ : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X) (c : Cns ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Cns ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i (μ ℓ n X i c δ))
      → Typ ℓ n X i (μ ℓ n X i c δ) p ↦
        Typ ℓ n X (Typ ℓ n X i c (μ-fst ℓ n X i c δ p))
          (δ (μ-fst ℓ n X i c δ p)) (μ-snd ℓ n X i c δ p)
    {-# REWRITE Typ-μ #-}

    --
    --  Monad Laws
    --

    μ-fst-η-pos : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Idx ℓ n X)
      → (δ : (p : Pos ℓ n X i (η ℓ n X i)) → Cns ℓ n X i)
      → (p : Pos ℓ n X i (μ ℓ n X i (η ℓ n X i) δ))
      → μ-fst ℓ n X i (η ℓ n X i) δ p ↦ η-pos ℓ n X i
    {-# REWRITE μ-fst-η-pos #-}

    -- μ-unit-l : (ℓ : Level) (n : ℕ)
    --   → (X : 𝕆Type ℓ n)
    --   → (i : Idx ℓ n X)
    --   → (δ : (p : Pos ℓ n X i (η ℓ n X i)) → Cns ℓ n X i)
    --   → μ ℓ n X i (η ℓ n X i) δ ↦ δ (η-pos ℓ n X i)
    -- {-# REWRITE μ-unit-l #-}
    

    
