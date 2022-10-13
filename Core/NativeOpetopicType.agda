{-# OPTIONS --opetopic-types #-}
--
--  OpetopicType.agda - Opetopic Types
--

open import Core.Prelude

module Core.NativeOpetopicType where

  postulate

    --
    --  Opetopic Types
    --

    𝕆Type : (ℓ : Level) (n : ℕ) 
      → Type (ℓ-suc ℓ)

    --
    --  Polynomial Structure
    --

    Frm : (ℓ : Level) (n : ℕ) 
      → 𝕆Type ℓ n → Type ℓ 

    Src : (ℓ : Level) (n : ℕ) 
      → (X : 𝕆Type ℓ n)
      → Frm ℓ n X → Type ℓ

    Pos : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i)
      → Type ℓ
      
    Typ : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i)
      → (p : Pos ℓ n X i c) → Frm ℓ n X 

    --
    --  Monadic Structure
    --

    η : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X)
      → Src ℓ n X i

    μ : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Src ℓ n X (Typ ℓ n X i c p))
      → Src ℓ n X i 

    --
    --  Position Intro
    --

    η-pos : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X)
      → Pos ℓ n X i (η ℓ n X i)

    μ-pos : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Src ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i c) (q : Pos ℓ n X (Typ ℓ n X i c p) (δ p))
      → Pos ℓ n X i (μ ℓ n X i c δ)

    --
    --  Position Elim
    --
    
    μ-fst : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Src ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i (μ ℓ n X i c δ))
      → Pos ℓ n X i c
      
    μ-snd : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Src ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i (μ ℓ n X i c δ))
      → Pos ℓ n X (Typ ℓ n X i c (μ-fst ℓ n X i c δ p))
          (δ (μ-fst ℓ n X i c δ p)) 

  --
  --  Native Bindings 
  --
  
  {-# BUILTIN OPETOPICTYPE 𝕆Type #-}
  {-# BUILTIN FRM Frm #-}
  {-# BUILTIN SRC Src #-}
  {-# BUILTIN POS Pos #-}
  {-# BUILTIN TYP Typ #-}
  {-# BUILTIN UNT η #-}
  {-# BUILTIN SUBST μ #-}
  {-# BUILTIN UNTPOS η-pos #-}
  {-# BUILTIN SUBSTPOS μ-pos #-}
  {-# BUILTIN SUBSTFST μ-fst #-}
  {-# BUILTIN SUBSTSND μ-snd #-}

  postulate

    --
    --  Position Computation Rules 
    --
    
    μ-fst-β : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Src ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i c) (q : Pos ℓ n X (Typ ℓ n X i c p) (δ p))
      → μ-fst ℓ n X i c δ (μ-pos ℓ n X i c δ p q) ↦ p
    {-# REWRITE μ-fst-β #-}
    
    μ-snd-β : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Src ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i c) (q : Pos ℓ n X (Typ ℓ n X i c p) (δ p))
      → μ-snd ℓ n X i c δ (μ-pos ℓ n X i c δ p q) ↦ q
    {-# REWRITE μ-snd-β #-}


    --
    --  Position Typing Rules
    --

    Typ-η : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X)
      → (p : Pos ℓ n X i (η ℓ n X i))
      → Typ ℓ n X i (η ℓ n X i) p ↦ i
    {-# REWRITE Typ-η #-}

    Typ-μ : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Src ℓ n X (Typ ℓ n X i c p))
      → (p : Pos ℓ n X i (μ ℓ n X i c δ))
      → Typ ℓ n X i (μ ℓ n X i c δ) p ↦
        Typ ℓ n X (Typ ℓ n X i c (μ-fst ℓ n X i c δ p))
          (δ (μ-fst ℓ n X i c δ p)) (μ-snd ℓ n X i c δ p)
    {-# REWRITE Typ-μ #-}

    --
    --  Left Unit Law
    --

    μ-unit-l : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n) (i : Frm ℓ n X)
      → (δ : (p : Pos ℓ n X i (η ℓ n X i)) → Src ℓ n X i)
      → μ ℓ n X i (η ℓ n X i) δ ↦ δ (η-pos ℓ n X i)
    {-# REWRITE μ-unit-l #-}

    μ-pos-unit-l : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n) (i : Frm ℓ n X)
      → (δ : (p : Pos ℓ n X i (η ℓ n X i)) → Src ℓ n X i)
      → (p : Pos ℓ n X i (η ℓ n X i)) (q : Pos ℓ n X i (δ (η-pos ℓ n X i)))
      → μ-pos ℓ n X i (η ℓ n X i) δ p q ↦ q
    {-# REWRITE μ-pos-unit-l #-}

    μ-fst-unit-l : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n) (i : Frm ℓ n X)
      → (δ : (p : Pos ℓ n X i (η ℓ n X i)) → Src ℓ n X i)
      → (p : Pos ℓ n X i (μ ℓ n X i (η ℓ n X i) δ))
      → μ-fst ℓ n X i (η ℓ n X i) δ p ↦ η-pos ℓ n X i
    {-# REWRITE μ-fst-unit-l #-}

    μ-snd-unit-l : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n) (i : Frm ℓ n X)
      → (δ : (p : Pos ℓ n X i (η ℓ n X i)) → Src ℓ n X i)
      → (p : Pos ℓ n X i (μ ℓ n X i (η ℓ n X i) δ))
      → μ-snd ℓ n X i (η ℓ n X i) δ p ↦ p
    {-# REWRITE μ-snd-unit-l #-}

    --
    --  Right Unit Law
    --

    μ-unit-r : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i)
      → μ ℓ n X i c (λ p → η ℓ n X (Typ ℓ n X i c p)) ↦ c
    {-# REWRITE μ-unit-r #-} 

    μ-pos-unit-r : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i) (p : Pos ℓ n X i c)
      → (q : Pos ℓ n X (Typ ℓ n X i c p) (η ℓ n X (Typ ℓ n X i c p)))
      → μ-pos ℓ n X i c (λ p → η ℓ n X (Typ ℓ n X i c p)) p q ↦ p
    {-# REWRITE μ-pos-unit-r #-}

    μ-fst-unit-r : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i) 
      → (p : Pos ℓ n X i (μ ℓ n X i c (λ p → η ℓ n X (Typ ℓ n X i c p))))
      → μ-fst ℓ n X i c (λ p → η ℓ n X (Typ ℓ n X i c p)) p ↦ p 
    {-# REWRITE μ-fst-unit-r #-}

    μ-snd-unit-r : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i) 
      → (p : Pos ℓ n X i (μ ℓ n X i c (λ p → η ℓ n X (Typ ℓ n X i c p))))
      → μ-snd ℓ n X i c (λ p → η ℓ n X (Typ ℓ n X i c p)) p ↦
        η-pos ℓ n X (Typ ℓ n X i c p)
    {-# REWRITE μ-snd-unit-r #-}

    --
    --  Associative Law
    --

    μ-assoc : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Src ℓ n X (Typ ℓ n X i c p))
      → (ϵ : (p : Pos ℓ n X i (μ ℓ n X i c δ))
           → Src ℓ n X (Typ ℓ n X i (μ ℓ n X i c δ) p))
      → μ ℓ n X i (μ ℓ n X i c δ) ϵ ↦
        μ ℓ n X i c (λ p → μ ℓ n X (Typ ℓ n X i c p) (δ p)
                    (λ q → ϵ (μ-pos ℓ n X i c δ p q)))
    {-# REWRITE μ-assoc #-} 

    μ-pos-assoc : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Src ℓ n X (Typ ℓ n X i c p))
      → (ϵ : (p : Pos ℓ n X i (μ ℓ n X i c δ))
           → Src ℓ n X (Typ ℓ n X i (μ ℓ n X i c δ) p))
      → (p : Pos ℓ n X i (μ ℓ n X i c δ))
      → (q : Pos ℓ n X (Typ ℓ n X i (μ ℓ n X i c δ) p) (ϵ p))
      → μ-pos ℓ n X i (μ ℓ n X i c δ) ϵ p q ↦
        μ-pos ℓ n X i c (λ p → μ ℓ n X (Typ ℓ n X i c p) (δ p)
                        (λ q → ϵ (μ-pos ℓ n X i c δ p q)))
                        (μ-fst ℓ n X i c δ p)
                        (μ-pos ℓ n X (Typ ℓ n X i c (μ-fst ℓ n X i c δ p)) (δ (μ-fst ℓ n X i c δ p))
                            (λ q → ϵ (μ-pos ℓ n X i c δ (μ-fst ℓ n X i c δ p) q))
                            (μ-snd ℓ n X i c δ p) q)
    {-# REWRITE μ-pos-assoc #-}

    μ-fst-assoc : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Src ℓ n X (Typ ℓ n X i c p))
      → (ϵ : (p : Pos ℓ n X i (μ ℓ n X i c δ))
           → Src ℓ n X (Typ ℓ n X i (μ ℓ n X i c δ) p))
      → (pqr : Pos ℓ n X i (μ ℓ n X i (μ ℓ n X i c δ) ϵ))
      → μ-fst ℓ n X i (μ ℓ n X i c δ) ϵ pqr ↦
        let p = μ-fst ℓ n X i c (λ p → μ ℓ n X (Typ ℓ n X i c p) (δ p)
                                 (λ q → ϵ (μ-pos ℓ n X i c δ p q))) pqr 
            qr = μ-snd ℓ n X i c (λ p → μ ℓ n X (Typ ℓ n X i c p) (δ p)
                                 (λ q → ϵ (μ-pos ℓ n X i c δ p q))) pqr
            q = μ-fst ℓ n X (Typ ℓ n X i c p) (δ p) (λ q → ϵ (μ-pos ℓ n X i c δ p q)) qr
        in μ-pos ℓ n X i c δ p q 
    {-# REWRITE μ-fst-assoc #-} 

    μ-snd-assoc : (ℓ : Level) (n : ℕ) (X : 𝕆Type ℓ n)
      → (i : Frm ℓ n X) (c : Src ℓ n X i)
      → (δ : (p : Pos ℓ n X i c) → Src ℓ n X (Typ ℓ n X i c p))
      → (ϵ : (p : Pos ℓ n X i (μ ℓ n X i c δ))
           → Src ℓ n X (Typ ℓ n X i (μ ℓ n X i c δ) p))
      → (pqr : Pos ℓ n X i (μ ℓ n X i (μ ℓ n X i c δ) ϵ))
      → μ-snd ℓ n X i (μ ℓ n X i c δ) ϵ pqr ↦
        let p = μ-fst ℓ n X i c (λ p → μ ℓ n X (Typ ℓ n X i c p) (δ p)
                                 (λ q → ϵ (μ-pos ℓ n X i c δ p q))) pqr 
            qr = μ-snd ℓ n X i c (λ p → μ ℓ n X (Typ ℓ n X i c p) (δ p)
                                 (λ q → ϵ (μ-pos ℓ n X i c δ p q))) pqr
        in μ-snd ℓ n X (Typ ℓ n X i c p) (δ p) (λ q → ϵ (μ-pos ℓ n X i c δ p q)) qr
    {-# REWRITE μ-snd-assoc #-} 
  

