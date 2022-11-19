{-# OPTIONS --local-confluence-check #-}
--
--  OpetopicType.agda - Opetopic Types
--

open import Core.Prelude

module Core.FreshOpetopicType where

  --
  --  Opetopic Types
  --

  postulate
  
    𝕆Type : (ℓ : Level) (n : ℕ) 
      → Type (ℓ-suc ℓ)

    --
    --  Polynomial Structure
    --
    
    Frm : (ℓ : Level) (n : ℕ) 
      → 𝕆Type ℓ n → Type ℓ 

    Pd : (ℓ : Level) (n : ℕ) 
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → Frm ℓ n X → Type ℓ

    Pos : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X P f)
      → Type ℓ 

    Typ : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X P f)
      → (p : Pos ℓ n X P f s) → Frm ℓ n X 

    Ihb : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X P f)
      → (p : Pos ℓ n X P f s)
      → P (Typ ℓ n X P f s p)

    --
    --  Monadic Structure
    --

    ν : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P Q : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X P f)
      → (ϕ : (p : Pos ℓ n X P f s) → Q (Typ ℓ n X P f s p))
      → Pd ℓ n X Q f

    η : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (x : P f)
      → Pd ℓ n X P f 

    μ : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X (Pd ℓ n X P) f)
      → Pd ℓ n X P f

    --
    --  Position Intro
    --
    
    ν-pos : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P Q : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X P f)
      → (ϕ : (p : Pos ℓ n X P f s) → Q (Typ ℓ n X P f s p))
      → Pos ℓ n X P f s → Pos ℓ n X Q f (ν ℓ n X P Q f s ϕ)

    η-pos : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (x : P f)
      → Pos ℓ n X P f (η ℓ n X P f x)

    μ-pos : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X (Pd ℓ n X P) f)
      → (p : Pos ℓ n X (Pd ℓ n X P) f s)
      → (q : Pos ℓ n X P (Typ ℓ n X (Pd ℓ n X P) f s p)
                         (Ihb ℓ n X (Pd ℓ n X P) f s p))
      → Pos ℓ n X P f (μ ℓ n X P f s)

    --
    --  Position Elim
    --
    
    ν-inv : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P Q : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X P f)
      → (ϕ : (p : Pos ℓ n X P f s) → Q (Typ ℓ n X P f s p))
      → Pos ℓ n X Q f (ν ℓ n X P Q f s ϕ) → Pos ℓ n X P f s

    η-pos-elim : (ℓ ℓ' : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (x : P f)
      → (Q : Pos ℓ n X P f (η ℓ n X P f x) → Type ℓ')
      → (q : Q (η-pos ℓ n X P f x))
      → (p : Pos ℓ n X P f (η ℓ n X P f x)) → Q p

    μ-fst : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X (Pd ℓ n X P) f)
      → (p : Pos ℓ n X P f (μ ℓ n X P f s))
      → Pos ℓ n X (Pd ℓ n X P) f s

    μ-snd : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X (Pd ℓ n X P) f)
      → (p : Pos ℓ n X P f (μ ℓ n X P f s))
      → Pos ℓ n X P (Typ ℓ n X (Pd ℓ n X P) f s (μ-fst ℓ n X P f s p))
                    (Ihb ℓ n X (Pd ℓ n X P) f s (μ-fst ℓ n X P f s p))

    --
    --  Position Computation
    --

    η-pos-elim-β : (ℓ ℓ' : Level) (n : ℕ) 
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (x : P f)
      → (Q : Pos ℓ n X P f (η ℓ n X P f x) → Type ℓ')
      → (q : Q (η-pos ℓ n X P f x))
      → η-pos-elim ℓ ℓ' n X P f x Q q (η-pos ℓ n X P f x) ↦ q
    {-# REWRITE η-pos-elim-β #-}

    ν-inv-β : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P Q : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X P f)
      → (ϕ : (p : Pos ℓ n X P f s) → Q (Typ ℓ n X P f s p))
      → (p : Pos ℓ n X P f s)
      → ν-inv ℓ n X P Q f s ϕ (ν-pos ℓ n X P Q f s ϕ p) ↦ p
    {-# REWRITE ν-inv-β #-} 

    ν-inv-η : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P Q : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X P f)
      → (ϕ : (p : Pos ℓ n X P f s) → Q (Typ ℓ n X P f s p))
      → (p : Pos ℓ n X Q f (ν ℓ n X P Q f s ϕ))
      → ν-pos ℓ n X P Q f s ϕ (ν-inv ℓ n X P Q f s ϕ p) ↦ p
    {-# REWRITE ν-inv-η #-} 

    μ-fst-β : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X (Pd ℓ n X P) f)
      → (p : Pos ℓ n X (Pd ℓ n X P) f s)
      → (q : Pos ℓ n X P (Typ ℓ n X (Pd ℓ n X P) f s p)
                         (Ihb ℓ n X (Pd ℓ n X P) f s p))
      → μ-fst ℓ n X P f s (μ-pos ℓ n X P f s p q) ↦ p
    {-# REWRITE μ-fst-β #-}

    μ-snd-β : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X (Pd ℓ n X P) f)
      → (p : Pos ℓ n X (Pd ℓ n X P) f s)
      → (q : Pos ℓ n X P (Typ ℓ n X (Pd ℓ n X P) f s p)
                         (Ihb ℓ n X (Pd ℓ n X P) f s p))
      → μ-snd ℓ n X P f s (μ-pos ℓ n X P f s p q) ↦ q
    {-# REWRITE μ-snd-β #-}

    μ-pos-η : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X (Pd ℓ n X P) f)
      → (p : Pos ℓ n X P f (μ ℓ n X P f s))
      → μ-pos ℓ n X P f s (μ-fst ℓ n X P f s p)
                          (μ-snd ℓ n X P f s p) ↦ p
    {-# REWRITE μ-pos-η #-}

    --
    --  Typing and Inhabitants
    --

    Typ-ν : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P Q : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X P f)
      → (ϕ : (p : Pos ℓ n X P f s) → Q (Typ ℓ n X P f s p))
      → (p : Pos ℓ n X Q f (ν ℓ n X P Q f s ϕ))
      → Typ ℓ n X Q f (ν ℓ n X P Q f s ϕ) p ↦
        Typ ℓ n X P f s (ν-inv ℓ n X P Q f s ϕ p)
    {-# REWRITE Typ-ν #-}

    Ihb-ν : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P Q : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X P f)
      → (ϕ : (p : Pos ℓ n X P f s) → Q (Typ ℓ n X P f s p))
      → (p : Pos ℓ n X Q f (ν ℓ n X P Q f s ϕ))
      → Ihb ℓ n X Q f (ν ℓ n X P Q f s ϕ) p ↦ ϕ (ν-inv ℓ n X P Q f s ϕ p)
    {-# REWRITE Ihb-ν #-}

    Typ-η : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (x : P f)
      → (p : Pos ℓ n X P f (η ℓ n  X P f x))
      → Typ ℓ n X P f (η ℓ n X P f x) p ↦ f
    {-# REWRITE Typ-η #-}

    Ihb-η : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (x : P f)
      → (p : Pos ℓ n X P f (η ℓ n X P f x))
      → Ihb ℓ n X P f (η ℓ n X P f x) p ↦ x
    {-# REWRITE Ihb-η #-}

    Typ-μ : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X (Pd ℓ n X P) f)
      → (p : Pos ℓ n X P f (μ ℓ n X P f s))
      → Typ ℓ n X P f (μ ℓ n X P f s) p ↦
        Typ ℓ n X P (Typ ℓ n X (Pd ℓ n X P) f s (μ-fst ℓ n X P f s p))
                (Ihb ℓ n X (Pd ℓ n X P) f s (μ-fst ℓ n X P f s p)) (μ-snd ℓ n X P f s p) 
    {-# REWRITE Typ-μ #-}

    Ihb-μ : (ℓ : Level) (n : ℕ)
      → (X : 𝕆Type ℓ n)
      → (P : Frm ℓ n X → Type ℓ)
      → (f : Frm ℓ n X) (s : Pd ℓ n X (Pd ℓ n X P) f)
      → (p : Pos ℓ n X P f (μ ℓ n X P f s))
      → Ihb ℓ n X P f (μ ℓ n X P f s) p ↦
        Ihb ℓ n X P (Typ ℓ n X (Pd ℓ n X P) f s (μ-fst ℓ n X P f s p))
                  (Ihb ℓ n X (Pd ℓ n X P) f s (μ-fst ℓ n X P f s p)) (μ-snd ℓ n X P f s p) 
    {-# REWRITE Ihb-μ #-}

    --
    --  Functoriality of ν 
    --

    -- ν-id : (ℓ : Level) (n : ℕ)
    --   → (X : 𝕆Type ℓ n)
    --   → (P : Frm ℓ n X → Type ℓ)
    --   → (f : Frm ℓ n X) (s : Pd ℓ n X P f)
    --   → ν ℓ n X P P f s (Ihb ℓ n X P f s) ↦ s
    -- {-# REWRITE ν-id #-}
    
    -- ν-ν : (ℓ : Level) (n : ℕ)
    --   → (X : 𝕆Type ℓ n)
    --   → (P Q R : Frm ℓ n X → Type ℓ)
    --   → (f : Frm ℓ n X) (s : Pd ℓ n X P f)
    --   → (ϕ : (p : Pos ℓ n X P f s) → Q (Typ ℓ n X P f s p))
    --   → (ψ : (p : Pos ℓ n X Q f (ν ℓ n X P Q f s ϕ))
    --            → R (Typ ℓ n X Q f (ν ℓ n X P Q f s ϕ) p))
    --   → ν ℓ n X Q R f (ν ℓ n X P Q f s ϕ) ψ ↦
    --     ν ℓ n X P R f s (λ p → ψ (ν-pos ℓ n X P Q f s ϕ p))
    -- {-# REWRITE ν-ν #-} 

    -- 
    -- Naturality Laws
    --
      
    -- ν-η : (ℓ : Level) (n : ℕ)
    --   → (X : 𝕆Type ℓ n)
    --   → (P Q : Frm ℓ n X → Type ℓ)
    --   → (f : Frm ℓ n X) (x : P f)
    --   → (ϕ : (p : Pos ℓ n X P f (η ℓ n X P f x)) → Q f)
    --   → ν ℓ n X P Q f (η ℓ n X P f x) ϕ ↦
    --     η ℓ n X Q f (ϕ (η-pos ℓ n X P f x)) 
    -- {-# REWRITE ν-η #-}

    -- ν-η-inv : (ℓ : Level) (n : ℕ)
    --   → (X : 𝕆Type ℓ n)
    --   → (P Q : Frm ℓ n X → Type ℓ)
    --   → (f : Frm ℓ n X) (x : P f)
    --   → (ϕ : (p : Pos ℓ n X P f (η ℓ n X P f x)) → Q f)
    --   → (p : Pos ℓ n X Q f (ν ℓ n X P Q f (η ℓ n X P f x) ϕ))
    --   → ν-inv ℓ n X P Q f (η ℓ n X P f x) ϕ p ↦
    --     η-pos ℓ n X P f x 
    -- {-# REWRITE ν-η-inv #-}

    -- ν-η-pos : (ℓ : Level) (n : ℕ)
    --   → (X : 𝕆Type ℓ n)
    --   → (P Q : Frm ℓ n X → Type ℓ)
    --   → (f : Frm ℓ n X) (x : P f)
    --   → (ϕ : (p : Pos ℓ n X P f (η ℓ n X P f x)) → Q f)
    --   → (p : Pos ℓ n X P f (η ℓ n X P f x))
    --   → ν-pos ℓ n X P Q f (η ℓ n X P f x) ϕ p ↦ 
    --     η-pos ℓ n X Q f {!!}
    -- {-# REWRITE ν-η-pos #-} 

    -- ν-μ : (ℓ : Level) (n : ℕ)
    --   → (X : 𝕆Type ℓ n)
    --   → (P Q : Frm ℓ n X → Type ℓ)
    --   → (f : Frm ℓ n X) (s : Pd ℓ n X (Pd ℓ n X P) f)
    --   → (ϕ : (p : Pos ℓ n X P f (μ ℓ n X P f s))
    --        → Q (Typ ℓ n X P f (μ ℓ n X P f s) p))
    --   → ν ℓ n X P Q f (μ ℓ n X P f s) ϕ ↦
    --     μ ℓ n X Q f (ν ℓ n X (Pd ℓ n X P) (Pd ℓ n X Q) f s
    --       (λ p → ν ℓ n X P Q (Typ ℓ n X (Pd ℓ n X P) f s p)
    --                      (Ihb ℓ n X (Pd ℓ n X P) f s p)
    --         (λ q → ϕ (μ-pos ℓ n X P f s p q)))) 
    -- {-# REWRITE ν-μ #-}

    --
    -- Monad Laws
    --

    -- μ-unit-l : (ℓ : Level) (n : ℕ)
    --   → (X : 𝕆Type ℓ n)
    --   → (P : Frm ℓ n X → Type ℓ)
    --   → (f : Frm ℓ n X) (s : Pd ℓ n X P f)
    --   → μ ℓ n X P f (η ℓ n X (Pd ℓ n X P) f s) ↦ s
    -- {-# REWRITE μ-unit-l #-}

    -- μ-unit-r : (ℓ : Level) (n : ℕ)
    --   → (X : 𝕆Type ℓ n)
    --   → (P : Frm ℓ n X → Type ℓ)
    --   → (f : Frm ℓ n X) (s : Pd ℓ n X P f)
    --   → μ ℓ n X P f (ν ℓ n X P (Pd ℓ n X P) f s
    --       (λ p → η ℓ n X P (Typ ℓ n X P f s p) (Ihb ℓ n X P f s p))) ↦ s
    -- {-# REWRITE μ-unit-r #-}

    -- μ-assoc : (ℓ : Level) (n : ℕ)
    --   → (X : 𝕆Type ℓ n)
    --   → (P : Frm ℓ n X → Type ℓ)
    --   → (f : Frm ℓ n X) (s : Pd ℓ n X (Pd ℓ n X (Pd ℓ n X P)) f)
    --   → μ ℓ n X P f (μ ℓ n X (Pd ℓ n X P) f s) ↦
    --     μ ℓ n X P f (ν ℓ n X (Pd ℓ n X (Pd ℓ n X P)) (Pd ℓ n X P) f s
    --       (λ p → μ ℓ n X P (Typ ℓ n X (Pd ℓ n X (Pd ℓ n X P)) f s p)
    --                    (Ihb ℓ n X (Pd ℓ n X (Pd ℓ n X P)) f s p))) 
    -- {-# REWRITE μ-assoc #-}

    --
    --  Position Compatibilities
    --

    
    -- ν-η : (ℓ : Level) (n : ℕ)
    --   → (X : 𝕆Type ℓ n)
    --   → (P Q : Frm ℓ n X → Type ℓ)
    --   → (f : Frm ℓ n X) (x : P f)
    --   → (ϕ : (p : Pos ℓ n X P f (η ℓ n X P f x)) → Q f)
    --   → ν ℓ n X P Q f (η ℓ n X P f x) ϕ ↦
    --     η ℓ n X Q f (ϕ (η-pos ℓ n X P f x)) 


      -- → ν ℓ n X P Q f (η ℓ n X P f x) ϕ ↦
      --   η ℓ n X Q f (ϕ (η-pos ℓ n X P f x)) 


  -- data Tr (ℓ : Level) (n : ℕ) 
  --     (X : 𝕆Type ℓ (suc n))
  --     (P : Frm ℓ (suc n) X → Type ℓ)
  --   : Frm ℓ (suc n) X → Type ℓ

  -- data TrPos (ℓ : Level) (n : ℕ) 
  --     (X : 𝕆Type ℓ (suc n))
  --     (P : Frm ℓ (suc n) X → Type ℓ)
  --   : (f : Frm ℓ (suc n) X) → Tr ℓ n X P f → Type ℓ

  -- TrTyp : (ℓ : Level) (n : ℕ)
  --   → (X : 𝕆Type ℓ (suc n))
  --   → (P : Frm ℓ (suc n) X → Type ℓ)
  --   → (f : Frm ℓ (suc n) X) (s : Pd ℓ (suc n) X P f)
  --   → (p : Pos ℓ (suc n) X P f s) → Frm ℓ (suc n) X 

  -- TrIhb : (ℓ : Level) (n : ℕ)
  --   → (X : 𝕆Type ℓ (suc n))
  --   → (P : Frm ℓ (suc n) X → Type ℓ)
  --   → (f : Frm ℓ (suc n) X) (s : Pd ℓ (suc n) X P f)
  --   → (p : Pos ℓ (suc n) X P f s)
  --   → P (TrTyp ℓ n X P f s p)

  --
  --
  --



  --
  --  Basic Definitions
  --

  -- 𝕆Type ℓ zero = 𝟙 (ℓ-suc ℓ)
  -- 𝕆Type ℓ (suc n) = 
  --   Σ[ X ∈ 𝕆Type ℓ n ]
  --   ((f : Frm ℓ n X) → Type ℓ)

  -- Frm ℓ zero X = 𝟙 ℓ 
  -- Frm ℓ (suc n) (X , P) = 
  --   Σ[ f ∈ Frm ℓ n X ]
  --   Σ[ src ∈ Pd ℓ n X P f ] 
  --   P f

  -- Pd ℓ zero X P f = P f
  -- Pd ℓ (suc n) X P f = Tr ℓ n X P f

  -- Pos ℓ zero X P f s = 𝟙 ℓ
  -- Pos ℓ (suc n) X P f s = TrPos ℓ n X P f s

  -- Typ ℓ zero X P f s p = ●
  -- Typ ℓ (suc n) X P f s p = TrTyp ℓ n X P f s p
  
  -- Ihb ℓ zero X P f s p = s
  -- Ihb ℓ (suc n) X P f s p = TrIhb ℓ n X P f s p

  -- data Tr ℓ n X P where 
  -- data TrPos ℓ n X P where
  -- TrTyp ℓ n X P = {!!}
  -- TrIhb ℓ n X P = {!!} 
