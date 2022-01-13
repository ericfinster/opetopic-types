{-# OPTIONS --without-K --rewriting --no-positivity #-}

open import MiniHoTT

module NewOpetopicType where

  --
  --  Opetopic Types
  --

  𝕆 : (ℓ : Level) → ℕ → Set (ℓ-suc ℓ)

  --
  --  Polynomial Signature
  --

  Frm : ∀ {ℓ n} → 𝕆 ℓ n → Set ℓ
  Cns : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → Frm X → Set ℓ
  Pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f) → Set ℓ
  Typ : ∀ {ℓ n} (X : 𝕆 ℓ n)
    → {f : Frm X} (c : Cns X f)
    → (p : Pos X c) → Frm X


  --
  --  Monadic Signature
  --
  
  postulate

    η : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X)
      → Cns X f 

    η-pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X)
      → Pos X (η X f) 

    η-pos-elim : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (P : (p : Pos X (η X f)) → Set ℓ)
      → (η-pos* : P (η-pos X f))
      → (p : Pos X (η X f)) → P p 

    μ : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → Cns X f

    μ-pos : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X c) (q : Pos X (δ p))
      → Pos X (μ X c δ) 

    μ-fst : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X (μ X c δ))
      → Pos X c

    μ-snd : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X (μ X c δ))
      → Pos X (δ (μ-fst X c δ p))
  
  postulate

    --
    --  Position Typing
    --

    η-pos-typ : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (p : Pos X (η X f))
      → Typ X (η X f) p ↦ f
    {-# REWRITE η-pos-typ #-}

    μ-pos-typ : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X c) (q : Pos X (δ p))
      → Typ X (μ X c δ) (μ-pos X c δ p q)
        ↦ Typ X (δ p) q
    {-# REWRITE μ-pos-typ #-}

    --
    --  Position Computation Rules
    --
    
    η-pos-elim-β : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (P : (p : Pos X (η X f)) → Set ℓ)
      → (η-pos* : P (η-pos X f))
      → η-pos-elim X f P η-pos* (η-pos X f) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}

    μ-pos-fst-β : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X c) (q : Pos X (δ p))
      → μ-fst X c δ (μ-pos X c δ p q) ↦ p
    {-# REWRITE μ-pos-fst-β #-}

    μ-pos-snd-β : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X c) (q : Pos X (δ p))
      → μ-snd X c δ (μ-pos X c δ p q) ↦ q
    {-# REWRITE μ-pos-snd-β #-}

    μ-pos-η : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → {f : Frm X} (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (p : Pos X (μ X c δ))
      → μ-pos X c δ (μ-fst X c δ p) (μ-snd X c δ p) ↦ p
    {-# REWRITE μ-pos-η #-}

    --
    --  Monad Laws
    --

    μ-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → μ X c (λ p → η X (Typ X c p)) ↦ c
    {-# REWRITE μ-unit-r #-}

    μ-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : (p : Pos X (η X f)) → Cns X (Typ X (η X f) p))
      → μ X (η X f) δ ↦ δ (η-pos X f)
    {-# REWRITE μ-unit-l #-}

    μ-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (δ : (p : Pos X c) → Cns X (Typ X c p))
      → (ε : (p : Pos X (μ X c δ)) → Cns X (Typ X (μ X c δ) p))
      → μ X (μ X c δ) ε ↦ 
        μ X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q)))
    {-# REWRITE μ-assoc #-}

    --
    --  Compatibilities of Intro/Elim with Reductions
    --

    -- Introduction
    μ-pos-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f) (p : Pos X c)
      → μ-pos X c (λ p → η X (Typ X c p)) p (η-pos X (Typ X c p)) ↦ p
    {-# REWRITE μ-pos-unit-r #-}    

    μ-pos-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : (p : Pos X (η X f)) → Cns X f)
      → (p : Pos X (δ (η-pos X f)))
      → μ-pos X (η X f) δ (η-pos X f) p ↦ p
    {-# REWRITE μ-pos-unit-l #-}

    -- μ-pos-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
    --   → (f : Frm X) (c : Cns X f)
    --   → (δ : (p : Pos X c) → Cns X (Typ X c p))
    --   → (ε : (p : Pos X (μ X c δ)) → Cns X (Typ X (μ X c δ) p))
    --   → (pq : Pos X (μ X c δ)) (r : Pos X (ε pq))
    --   → let p₀ = μ-fst X c δ pq
    --         q₀ = μ-snd X c δ pq 
    --     in μ-pos X (μ X c δ) ε pq r
    --       ↦ μ-pos X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q)))
    --           p₀ (μ-pos X (δ p₀) (λ q → ε (μ-pos X c δ p₀ q)) q₀ r)
    
    -- First Projection
    μ-fst-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (p : Pos X (μ X c (λ p → η X (Typ X c p))))
      → μ-fst X c (λ p → η X (Typ X c p)) p ↦ p
    {-# REWRITE μ-fst-unit-r #-}

    μ-fst-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : (p : Pos X (η X f)) → Cns X f)
      → (p : Pos X (μ X (η X f) δ))
      → μ-fst X (η X f) δ p ↦ η-pos X f
    {-# REWRITE μ-fst-unit-l #-}

    -- μ-fst-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
    --   → (f : Frm X) (c : Cns X f)
    --   → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
    --   → (ε : {g : Frm X} (p : Pos X (μ X c δ) g) → Cns X g)
    --   → {g : Frm X} (pqr : Pos X (μ X (μ X c δ) ε) g)
    --   → let p = μ-fst X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
    --         qr = μ-snd X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
    --         q = μ-fst X (δ p) (λ q → ε (μ-pos X c δ p q)) qr
    --     in μ-fst X (μ X c δ) ε pqr ↦ μ-pos X c δ p q  
    -- {-# REWRITE μ-fst-assoc #-}

    -- Second Projection
    μ-snd-unit-r : ∀ {ℓ n} (X : 𝕆 ℓ n)
      → (f : Frm X) (c : Cns X f)
      → (p : Pos X (μ X c (λ p → η X (Typ X c p))))
      → μ-snd X c (λ p → η X (Typ X c p)) p ↦ η-pos X (Typ X c p)
    {-# REWRITE μ-snd-unit-r #-}

    μ-snd-unit-l : ∀ {ℓ n} (X : 𝕆 ℓ n) (f : Frm X)
      → (δ : (p : Pos X (η X f)) → Cns X (Typ X (η X f) p))
      → (p : Pos X (μ X (η X f) δ))
      → μ-snd X (η X f) δ p ↦ p
    {-# REWRITE μ-snd-unit-l #-}

    -- μ-snd-assoc : ∀ {ℓ n} (X : 𝕆 ℓ n)
    --   → (f : Frm X) (c : Cns X f)
    --   → (δ : {g : Frm X} (p : Pos X c g) → Cns X g)
    --   → (ε : {g : Frm X} (p : Pos X (μ X c δ) g) → Cns X g)
    --   → {g : Frm X} (pqr : Pos X (μ X (μ X c δ) ε) g)
    --   → let p = μ-fst X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
    --         qr = μ-snd X c (λ p → μ X (δ p) (λ q → ε (μ-pos X c δ p q))) pqr
    --     in μ-snd X (μ X c δ) ε pqr
    --       ↦ μ-snd X (δ p) (λ q → ε (μ-pos X c δ p q)) qr 
    -- {-# REWRITE μ-snd-assoc #-} 


  𝕆 = {!!} 

  Frm = {!!} 
  Cns = {!!}
  Pos = {!!}
  Typ = {!!} 
