{-# OPTIONS --no-positivity-check --no-termination-check #-}
--
--  OpetopicType.agda - Opetopic Types
--

open import Core.Prelude

module Core.OpetopicType where

  --
  --  Opetopic Types
  --

  𝕆Type : (n : ℕ) (ℓ : Level)
    → Type (ℓ-suc ℓ)

  Frm : (n : ℕ) (ℓ : Level)
    → 𝕆Type n ℓ → Type ℓ 

  Pd : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P : Frm n ℓ X → Type ℓ)
    → Frm n ℓ X → Type ℓ

  Pos : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P : Frm n ℓ X → Type ℓ)
    → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
    → Type ℓ 

  Typ : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P : Frm n ℓ X → Type ℓ)
    → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
    → (p : Pos n ℓ X P f ρ) → Frm n ℓ X 

  Ihb : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P : Frm n ℓ X → Type ℓ)
    → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
    → (p : Pos n ℓ X P f ρ)
    → P (Typ n ℓ X P f ρ p)

  postulate
  
    --
    --  Monadic Structure
    --

    ν : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f ρ) → Q (Typ n ℓ X P f ρ p))
      → Pd n ℓ X Q f

    η : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (x : P f)
      → Pd n ℓ X P f 

    μ : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X (Pd n ℓ X P) f)
      → Pd n ℓ X P f 

    --
    --  Position Intro 
    --

    ν-pos : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f ρ) → Q (Typ n ℓ X P f ρ p))
      → Pos n ℓ X P f ρ → Pos n ℓ X Q f (ν n ℓ X P Q f ρ ϕ)

    η-pos : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (x : P f)
      → Pos n ℓ X P f (η n ℓ X P f x)

    μ-pos : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X (Pd n ℓ X P) f ρ)
      → (q : Pos n ℓ X P (Typ n ℓ X (Pd n ℓ X P) f ρ p)
                         (Ihb n ℓ X (Pd n ℓ X P) f ρ p))
      → Pos n ℓ X P f (μ n ℓ X P f ρ)

    --
    --  Position Elim
    --

    ν-lift : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f ρ) → Q (Typ n ℓ X P f ρ p))
      → Pos n ℓ X Q f (ν n ℓ X P Q f ρ ϕ) → Pos n ℓ X P f ρ

    η-pos-elim : (n : ℕ) (ℓ ℓ' : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (x : P f)
      → (Q : Pos n ℓ X P f (η n ℓ X P f x) → Type ℓ')
      → (q : Q (η-pos n ℓ X P f x))
      → (p : Pos n ℓ X P f (η n ℓ X P f x)) → Q p

    μ-fst : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X P f (μ n ℓ X P f ρ))
      → Pos n ℓ X (Pd n ℓ X P) f ρ

    μ-snd : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X P f (μ n ℓ X P f ρ))
      → Pos n ℓ X P (Typ n ℓ X (Pd n ℓ X P) f ρ (μ-fst n ℓ X P f ρ p))
                    (Ihb n ℓ X (Pd n ℓ X P) f ρ (μ-fst n ℓ X P f ρ p))

    --
    --  Position Computation
    --

    η-pos-elim-β : (n : ℕ) (ℓ ℓ' : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (x : P f)
      → (Q : Pos n ℓ X P f (η n ℓ X P f x) → Type ℓ')
      → (q : Q (η-pos n ℓ X P f x))
      → η-pos-elim n ℓ ℓ' X P f x Q q (η-pos n ℓ X P f x) ↦ q
    {-# REWRITE η-pos-elim-β #-}

    ν-lift-β : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f ρ) → Q (Typ n ℓ X P f ρ p))
      → (p : Pos n ℓ X P f ρ)
      → ν-lift n ℓ X P Q f ρ ϕ (ν-pos n ℓ X P Q f ρ ϕ p) ↦ p
    {-# REWRITE ν-lift-β #-} 

    ν-lift-η : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f ρ) → Q (Typ n ℓ X P f ρ p))
      → (p : Pos n ℓ X Q f (ν n ℓ X P Q f ρ ϕ))
      → ν-pos n ℓ X P Q f ρ ϕ (ν-lift n ℓ X P Q f ρ ϕ p) ↦ p
    {-# REWRITE ν-lift-η #-} 

    μ-fst-β : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X (Pd n ℓ X P) f ρ)
      → (q : Pos n ℓ X P (Typ n ℓ X (Pd n ℓ X P) f ρ p)
                         (Ihb n ℓ X (Pd n ℓ X P) f ρ p))
      → μ-fst n ℓ X P f ρ (μ-pos n ℓ X P f ρ p q) ↦ p
    {-# REWRITE μ-fst-β #-}

    μ-snd-β : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X (Pd n ℓ X P) f ρ)
      → (q : Pos n ℓ X P (Typ n ℓ X (Pd n ℓ X P) f ρ p)
                         (Ihb n ℓ X (Pd n ℓ X P) f ρ p))
      → μ-snd n ℓ X P f ρ (μ-pos n ℓ X P f ρ p q) ↦ q
    {-# REWRITE μ-snd-β #-}

    μ-pos-η : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X P f (μ n ℓ X P f ρ))
      → μ-pos n ℓ X P f ρ (μ-fst n ℓ X P f ρ p)
                          (μ-snd n ℓ X P f ρ p) ↦ p
    {-# REWRITE μ-pos-η #-}

    --
    --  Typing and Inhabitants
    --

    Typ-ν : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f ρ) → Q (Typ n ℓ X P f ρ p))
      → (p : Pos n ℓ X Q f (ν n ℓ X P Q f ρ ϕ))
      → Typ n ℓ X Q f (ν n ℓ X P Q f ρ ϕ) p ↦
        Typ n ℓ X P f ρ (ν-lift n ℓ X P Q f ρ ϕ p)
    {-# REWRITE Typ-ν #-}

    Ihb-ν : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f ρ) → Q (Typ n ℓ X P f ρ p))
      → (p : Pos n ℓ X Q f (ν n ℓ X P Q f ρ ϕ))
      → Ihb n ℓ X Q f (ν n ℓ X P Q f ρ ϕ) p ↦ ϕ (ν-lift n ℓ X P Q f ρ ϕ p)
    {-# REWRITE Ihb-ν #-}

    Typ-η : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (x : P f)
      → (p : Pos n ℓ X P f (η n ℓ  X P f x))
      → Typ n ℓ X P f (η n ℓ X P f x) p ↦ f
    {-# REWRITE Typ-η #-}

    Ihb-η : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (x : P f)
      → (p : Pos n ℓ X P f (η n ℓ X P f x))
      → Ihb n ℓ X P f (η n ℓ X P f x) p ↦ x
    {-# REWRITE Ihb-η #-}

    Typ-μ : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X P f (μ n ℓ X P f ρ))
      → Typ n ℓ X P f (μ n ℓ X P f ρ) p ↦
        Typ n ℓ X P (Typ n ℓ X (Pd n ℓ X P) f ρ (μ-fst n ℓ X P f ρ p))
                (Ihb n ℓ X (Pd n ℓ X P) f ρ (μ-fst n ℓ X P f ρ p)) (μ-snd n ℓ X P f ρ p) 
    {-# REWRITE Typ-μ #-}

    Ihb-μ : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X (Pd n ℓ X P) f)
      → (p : Pos n ℓ X P f (μ n ℓ X P f ρ))
      → Ihb n ℓ X P f (μ n ℓ X P f ρ) p ↦
        Ihb n ℓ X P (Typ n ℓ X (Pd n ℓ X P) f ρ (μ-fst n ℓ X P f ρ p))
                  (Ihb n ℓ X (Pd n ℓ X P) f ρ (μ-fst n ℓ X P f ρ p)) (μ-snd n ℓ X P f ρ p) 
    {-# REWRITE Ihb-μ #-}

    --
    --  Functoriality of ν 
    --

    ν-id : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → ν n ℓ X P P f ρ (Ihb n ℓ X P f ρ) ↦ ρ
    {-# REWRITE ν-id #-}
    
    ν-ν : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q R : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → (ϕ : (p : Pos n ℓ X P f ρ) → Q (Typ n ℓ X P f ρ p))
      → (ψ : (p : Pos n ℓ X Q f (ν n ℓ X P Q f ρ ϕ))
               → R (Typ n ℓ X Q f (ν n ℓ X P Q f ρ ϕ) p))
      → ν n ℓ X Q R f (ν n ℓ X P Q f ρ ϕ) ψ ↦
        ν n ℓ X P R f ρ (λ p → ψ (ν-pos n ℓ X P Q f ρ ϕ p))
    {-# REWRITE ν-ν #-} 

    -- 
    -- Naturality Laws
    --
      
    ν-η : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (x : P f)
      → (ϕ : (p : Pos n ℓ X P f (η n ℓ X P f x)) → Q f)
      → ν n ℓ X P Q f (η n ℓ X P f x) ϕ ↦
        η n ℓ X Q f (ϕ (η-pos n ℓ X P f x)) 
    {-# REWRITE ν-η #-}

    ν-μ : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P Q : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X (Pd n ℓ X P) f)
      → (ϕ : (p : Pos n ℓ X P f (μ n ℓ X P f ρ))
           → Q (Typ n ℓ X P f (μ n ℓ X P f ρ) p))
      → ν n ℓ X P Q f (μ n ℓ X P f ρ) ϕ ↦
        μ n ℓ X Q f (ν n ℓ X (Pd n ℓ X P) (Pd n ℓ X Q) f ρ
          (λ p → ν n ℓ X P Q (Typ n ℓ X (Pd n ℓ X P) f ρ p)
                         (Ihb n ℓ X (Pd n ℓ X P) f ρ p)
            (λ q → ϕ (μ-pos n ℓ X P f ρ p q)))) 
    {-# REWRITE ν-μ #-}

    --
    -- Monad Laws
    --

    μ-unit-l : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → μ n ℓ X P f (η n ℓ X (Pd n ℓ X P) f ρ) ↦ ρ
    {-# REWRITE μ-unit-l #-}

    μ-unit-r : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X P f)
      → μ n ℓ X P f (ν n ℓ X P (Pd n ℓ X P) f ρ
          (λ p → η n ℓ X P (Typ n ℓ X P f ρ p) (Ihb n ℓ X P f ρ p))) ↦ ρ
    {-# REWRITE μ-unit-r #-}

    μ-assoc : (n : ℕ) (ℓ : Level)
      → (X : 𝕆Type n ℓ)
      → (P : Frm n ℓ X → Type ℓ)
      → (f : Frm n ℓ X) (ρ : Pd n ℓ X (Pd n ℓ X (Pd n ℓ X P)) f)
      → μ n ℓ X P f (μ n ℓ X (Pd n ℓ X P) f ρ) ↦
        μ n ℓ X P f (ν n ℓ X (Pd n ℓ X (Pd n ℓ X P)) (Pd n ℓ X P) f ρ
          (λ p → μ n ℓ X P (Typ n ℓ X (Pd n ℓ X (Pd n ℓ X P)) f ρ p)
                       (Ihb n ℓ X (Pd n ℓ X (Pd n ℓ X P)) f ρ p))) 
    {-# REWRITE μ-assoc #-}

    --
    -- Position Compatibilities
    --

    -- In fact, I now realize that there are really a lot of these
    -- that you are missing: for every equation involving μ, η and ν,
    -- there needs to be a corresponding equation for both the intro
    -- and the elim of their positions.

    --   ν-pos-id : (n : ℕ) (ℓ : Level)
    --     → (X : 𝕆Type n ℓ)
    --     → (P : Frm n ℓ X → Type ℓ)
    --     → (f : Frm n ℓ X) (s : Pd n ℓ X P f) (p : Pos n ℓ X P s)
    --     → ν-pos {Q = P} s (_⊚_ s) p ↦ p
    --   {-# REWRITE ν-pos-id #-}

    --   ν-lift-id : (n : ℕ) (ℓ : Level)
    --     → (X : 𝕆Type n ℓ)
    --     → (P : Frm n ℓ X → Type ℓ)
    --     → (f : Frm n ℓ X) (s : Pd n ℓ X P f) (p : Pos n ℓ X P s)
    --     → ν-lift {Q = P} s (_⊚_ s) p ↦ p 
    --   {-# REWRITE ν-lift-id #-}

    --   ν-pos-comp : (n : ℕ) (ℓ : Level)
    --     → (X : 𝕆Type n ℓ)
    --     → (P Q R : Frm n ℓ X → Type ℓ)
    --     → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
    --     → (ϕ : (p : Pos n ℓ X P s) → Q (Typ n ℓ X P f s p))
    --     → (ψ : (p : Pos Q (ν X P Q f s ϕ)) → R (Typ Q (ν X P Q f s ϕ) p))
    --     → (p : Pos n ℓ X P s)
    --     → ν-pos {Q = R} (ν {Q = Q} s ϕ) ψ (ν-pos s ϕ p) ↦
    --       ν-pos {Q = R} s (λ p → ψ (ν-pos s ϕ p)) p 
    --   {-# REWRITE ν-pos-comp #-}

    --   ν-lift-comp : (n : ℕ) (ℓ : Level)
    --     → (X : 𝕆Type n ℓ)
    --     → (P Q R : Frm n ℓ X → Type ℓ)
    --     → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
    --     → (ϕ : (p : Pos n ℓ X P s) → Q (Typ n ℓ X P f s p))
    --     → (ψ : (p : Pos Q (ν X P Q f s ϕ)) → R (Typ Q (ν X P Q f s ϕ) p))
    --     → (p : Pos R (ν {Q = R} (ν X P Q f s ϕ) ψ))
    --     → ν-lift {Q = Q} s ϕ (ν-lift (ν X P Q f s ϕ) ψ p) ↦
    --       ν-lift {Q = R} s (λ p → ψ (ν-pos s ϕ p)) p 
    --   {-# REWRITE ν-lift-comp #-}

  --
  --  Convenience map and bind functions 
  --

  ν-map : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P Q : Frm n ℓ X → Type ℓ)
    → (ϕ : {f : Frm n ℓ X} → P f → Q f)
    → (f : Frm n ℓ X) → Pd n ℓ X P f → Pd n ℓ X Q f
  ν-map n ℓ X P Q ϕ f s =
    ν n ℓ X P Q f s
      (λ p → ϕ (Ihb n ℓ X P f s p))

  ν-bind : (n : ℕ) (ℓ : Level)
    → (X : 𝕆Type n ℓ)
    → (P Q : Frm n ℓ X → Type ℓ)
    → (ϕ : {f : Frm n ℓ X} → P f → Pd n ℓ X Q f)
    → (f : Frm n ℓ X) → Pd n ℓ X P f → Pd n ℓ X Q f
  ν-bind n ℓ X P Q ϕ f s =
    μ n ℓ X Q f (ν n ℓ X P (Pd n ℓ X Q) f s
                  (λ p → ϕ (Ihb n ℓ X P f s p)))

  --
  --  Definitions of opeotpic types and frames
  --

  𝕆Type zero ℓ = 𝟙 (ℓ-suc ℓ)
  𝕆Type (suc n) ℓ =
    Σ[ X ∈ 𝕆Type n ℓ ]
    ((f : Frm n ℓ X) → Type ℓ)

  Frm zero ℓ X = 𝟙 ℓ
  Frm (suc n) ℓ (X , P) = 
    Σ[ f ∈ Frm n ℓ X ]
    Σ[ src ∈ Pd n ℓ X P f ] 
    P f

  --
  --  Pasting Diagrams and their Positions 
  --

  module _ (n : ℕ) (ℓ : Level)
    (X : 𝕆Type n ℓ)
    (P : Frm n ℓ X → Type ℓ)
    (U : Frm (suc n) ℓ (X , P) → Type ℓ) where

    data Tr : Frm (suc n) ℓ (X , P) → Type ℓ

    Branch : Frm n ℓ X → Type ℓ
    Branch f = Σ[ t ∈ P f ]
               Σ[ s ∈ Pd n ℓ X P f ]
               Tr (f , s , t)

    data Tr where

      lf : (frm : Frm n ℓ X) (tgt : P frm)
         → Tr (frm , η n ℓ X P frm tgt , tgt) 

      nd : (frm : Frm n ℓ X) (tgt : P frm)
         → (brs : Pd n ℓ X Branch frm)
         → (flr : U (frm , ν-map n ℓ X Branch P fst frm brs , tgt)) 
         → Tr (frm , ν-bind n ℓ X Branch P (λ b → fst (snd b)) frm brs , tgt)

    data TrPos : (f : Frm (suc n) ℓ (X , P)) → Tr f → Type ℓ where

      nd-here : {frm : Frm n ℓ X} {tgt : P frm}
        → {brs : Pd n ℓ X Branch frm}
        → {flr : U (frm , ν-map n ℓ X Branch P fst frm brs , tgt)}
        → TrPos (frm , ν-bind n ℓ X Branch P (λ b → fst (snd b)) frm brs , tgt)
                (nd frm tgt brs flr)

      nd-there : {frm : Frm n ℓ X} {tgt : P frm}
        → {brs : Pd n ℓ X Branch frm}
        → {flr : U (frm , ν-map n ℓ X Branch P fst frm brs , tgt)}
        → (p : Pos n ℓ X Branch frm brs)
        → (q : TrPos (Typ n ℓ X Branch frm brs p ,
                       fst (Ihb n ℓ X Branch frm brs p .snd) ,
                       fst (Ihb n ℓ X Branch frm brs p))
                      (Ihb n ℓ X Branch frm brs p .snd .snd))
        → TrPos (frm , ν-bind n ℓ X Branch P (λ b → fst (snd b)) frm brs , tgt)
                (nd frm tgt brs flr)

  --   γ : {frm : Frm n ℓ X} {src : Pd n ℓ X P frm} {tgt : P frm}
  --     → (pd : PdTr (frm , src , tgt ))
  --     → (brs : (p : Pos n ℓ X P f src) → Branch (src ⊚ p))
  --     → PdTr (frm , μ P (ν src λ p → lvs (brs p)) , tgt)

  --   γ-brs : {frm : Frm n ℓ X} {src : Pd n ℓ X P frm} (lbrs : Dec Branch src)
  --     → (brs : (p : Pos n ℓ X P (canopy lbrs)) → Branch (canopy lbrs ⊚ p))
  --     → (p : Pos n ℓ X P f src) → Branch (src ⊚ p)
  --   γ-brs lbrs brs p = [ μ P (ν (lvs (lbrs ⊛ p)) (λ q → lvs (brs (canopy-pos lbrs p q))))
  --                      , γ (br (lbrs ⊛ p)) (λ q → brs (canopy-pos lbrs p q))
  --                      ]

  --   γ (lf tgt) brs = br (brs (η-pos P tgt))
  --   γ (nd src tgt flr lbrs) brs =
  --     nd src tgt flr (λ-dec Branch src (γ-brs lbrs brs))

  --   γ-inl : {frm : Frm n ℓ X} {src : Pd n ℓ X P frm} {tgt : P frm}
  --     → (pd : PdTr (frm , src , tgt ))
  --     → (brs : (p : Pos n ℓ X P f src) → Branch (src ⊚ p))
  --     → (p : TrPos pd) → TrPos (γ pd brs)
  --   γ-inl (nd src tgt flr lbrs) brs nd-here = nd-here
  --   γ-inl (nd src tgt flr lbrs) brs (nd-there p q) =
  --     nd-there p (γ-inl (br (lbrs ⊛ p)) (λ q → brs (canopy-pos lbrs p q)) q) 

  --   γ-inr : {frm : Frm n ℓ X} {src : Pd n ℓ X P frm} {tgt : P frm}
  --     → (pd : PdTr (frm , src , tgt ))
  --     → (brs : (p : Pos n ℓ X P f src) → Branch (src ⊚ p))
  --     → (p : Pos n ℓ X P f src) (q : TrPos (br (brs p)))
  --     → TrPos (γ pd brs)
  --   γ-inr (lf tgt) brs p q = 
  --     η-pos-elim tgt (λ p → TrPos (br (brs p)) → TrPos (br (brs (η-pos P tgt)))) (λ x → x) p q
  --   γ-inr (nd src tgt flr lbrs) brs pq r = 
  --     let p = canopy-fst lbrs pq
  --         q = canopy-snd lbrs pq
  --     in nd-there p (γ-inr (br (lbrs ⊛ p)) (λ q → brs (canopy-pos lbrs p q)) q r)

  --   γ-pos-elim : {frm : Frm n ℓ X} {src : Pd n ℓ X P frm} {tgt : P frm}
  --     → (pd : PdTr (frm , src , tgt ))
  --     → (brs : (p : Pos n ℓ X P f src) → Branch (src ⊚ p))
  --     → ∀ {ℓ'} (B : TrPos (γ pd brs) → Type ℓ')
  --     → (inl* : (p : TrPos pd) → B (γ-inl pd brs p))
  --     → (inr* : (p : Pos n ℓ X P f src) (q : TrPos (br (brs p))) → B (γ-inr pd brs p q))
  --     → (p : TrPos (γ pd brs)) → B p
  --   γ-pos-elim (lf tgt) brs B inl* inr* p = inr* (η-pos P tgt) p
  --   γ-pos-elim (nd src tgt flr lbrs) brs B inl* inr* nd-here = inl* nd-here
  --   γ-pos-elim (nd src tgt flr lbrs) brs B inl* inr* (nd-there u v) = 
  --     γ-pos-elim (br (lbrs ⊛ u)) (λ q → brs (canopy-pos lbrs u q))
  --        (λ v' → B (nd-there u v')) (λ q → inl* (nd-there u q))
  --        (λ q → inr* (canopy-pos lbrs u q)) v
    
  --   postulate

  --     γ-pos-elim-inl-β : {frm : Frm n ℓ X} {src : Pd n ℓ X P frm} {tgt : P frm}
  --       → (pd : PdTr (frm , src , tgt ))
  --       → (brs : (p : Pos n ℓ X P f src) → Branch (src ⊚ p))
  --       → ∀ {ℓ'} (B : TrPos (γ pd brs) → Type ℓ')
  --       → (inl* : (p : TrPos pd) → B (γ-inl pd brs p))
  --       → (inr* : (p : Pos n ℓ X P f src) (q : TrPos (br (brs p))) → B (γ-inr pd brs p q))
  --       → (p : TrPos pd)
  --       → γ-pos-elim pd brs B inl* inr* (γ-inl pd brs p) ↦ inl* p
  --     {-# REWRITE γ-pos-elim-inl-β #-}
        
  --     γ-pos-elim-inr-β : {frm : Frm n ℓ X} {src : Pd n ℓ X P frm} {tgt : P frm}
  --       → (pd : PdTr (frm , src , tgt ))
  --       → (brs : (p : Pos n ℓ X P f src) → Branch (src ⊚ p))
  --       → ∀ {ℓ'} (B : TrPos (γ pd brs) → Type ℓ')
  --       → (inl* : (p : TrPos pd) → B (γ-inl pd brs p))
  --       → (inr* : (p : Pos n ℓ X P f src) (q : TrPos (br (brs p))) → B (γ-inr pd brs p q))
  --       → (p : Pos n ℓ X P f src) (q : TrPos (br (brs p)))
  --       → γ-pos-elim pd brs B inl* inr* (γ-inr pd brs p q) ↦ inr* p q
  --     {-# REWRITE γ-pos-elim-inr-β #-}

  Pd zero ℓ X P f = P ●
  Pd (suc n) ℓ (X , P) U = Tr n ℓ X P U

  Pos zero ℓ X P f ρ = 𝟙 ℓ
  Pos (suc n) ℓ (X , P) U = TrPos n ℓ X P U
  
  Typ zero ℓ X P f ρ p = ●
  Typ (suc n) ℓ (X , P) U ._ (nd frm tgt brs flr) nd-here =
    frm , ν-map n ℓ X (Branch n ℓ X P U) P fst frm brs , tgt 
  Typ (suc n) ℓ (X , P) U ._ (nd frm tgt brs flr) (nd-there p q) = 
    Typ (suc n) ℓ (X , P) U
      (Typ n ℓ X (Branch n ℓ X P U) frm brs p ,
        fst (Ihb n ℓ X (Branch n ℓ X P U) frm brs p .snd) ,
        fst (Ihb n ℓ X (Branch n ℓ X P U) frm brs p))
      (Ihb n ℓ X (Branch n ℓ X P U) frm brs p .snd .snd) q
  
  Ihb zero ℓ X P f ρ p = ρ
  Ihb (suc n) ℓ (X , P) U ._ (nd frm tgt brs flr) nd-here = flr
  Ihb (suc n) ℓ (X , P) U ._ (nd frm tgt brs flr) (nd-there p q) = 
    Ihb (suc n) ℓ (X , P) U
      (Typ n ℓ X (Branch n ℓ X P U) frm brs p ,
        fst (Ihb n ℓ X (Branch n ℓ X P U) frm brs p .snd) ,
        fst (Ihb n ℓ X (Branch n ℓ X P U) frm brs p))
      (Ihb n ℓ X (Branch n ℓ X P U) frm brs p .snd .snd) q

  --
  --  TODO: redo
  --

  -- ν {zero} s ϕ = ϕ tt*
  -- ν {suc n} (lf tgt) ϕ = lf tgt
  -- ν {suc n} {X = X , P} (nd src tgt flr brs) ϕ =
  --   nd src tgt (ϕ nd-here) (λ-dec (Branch _) src λ p →
  --     [ lvs (brs ⊛ p) , (ν {suc n} (br (brs ⊛ p)) (λ q → ϕ (nd-there p q))) ])

  -- ν-pos {zero} s ϕ p = tt*
  -- ν-pos {suc n} (nd src tgt flr brs) ϕ nd-here = nd-here
  -- ν-pos {suc n} (nd src tgt flr brs) ϕ (nd-there p q) =
  --   nd-there p (ν-pos (br (brs ⊛ p)) (λ q → ϕ (nd-there p q)) q)

  -- ν-lift {zero} s ϕ p = tt*
  -- ν-lift {suc n} (nd src tgt flr brs) ϕ nd-here = nd-here
  -- ν-lift {suc n} (nd src tgt flr brs) ϕ (nd-there p q) =
  --   nd-there p (ν-lift (br (brs ⊛ p)) (λ q → ϕ (nd-there p q)) q)

  -- η-dec : (n : ℕ) (ℓ : Level)
      -- → (X : 𝕆Type n ℓ)
  --   → (P : Frm n ℓ X → Type ℓ)
  --   → (U : Frm (X , P) → Type ℓ)
  --   → (f : Frm n ℓ X) (s : Pd n ℓ X P f)
  --   → Dec {X = X} (Branch U) s
  -- η-dec {X = X} {P} U s =
  --   λ-dec {X = X} {P} (Branch U) s
  --     (λ p → [ η P (s ⊚ p) , lf (s ⊚ p) ])

  -- η {zero} P x = x
  -- η {suc n} {X = X , P} U {f = _ , src , tgt} x =
  --   nd src tgt x (η-dec U src)

  -- η-pos {zero} P x = tt*
  -- η-pos {suc n} {X = X , P} U {f = _ , src , tgt} x = nd-here

  -- η-pos-elim {zero} x Q q p = q
  -- η-pos-elim {suc n} x Q q nd-here = q
  
  -- μ-brs : (n : ℕ) (ℓ : Level)
      -- → (X : 𝕆Type n ℓ) (P : Frm n ℓ X → Type ℓ)
  --   → (U : Frm (X , P) → Type ℓ)
  --   → (f : Frm n ℓ X) {src : Pd n ℓ X P f}
  --   → (brs : Dec {P = P} (Branch (PdTr U)) src)
  --   → (p : Pos n ℓ X P f src) → Branch U (src ⊚ p)
  -- μ-brs U brs p = [ lvs (brs ⊛ p) , μ U (br (brs ⊛ p)) ] 

  -- μ {zero} P s = s
  -- μ {suc n} U (lf tgt) = lf tgt
  -- μ {suc n} U (nd src tgt flr brs) =
  --   γ U flr (μ-brs U brs) 

  -- μ-pos {zero} P s p q = tt*
  -- μ-pos {suc n} U (nd src tgt flr brs) nd-here r =
  --   γ-inl U flr (μ-brs U brs) r
  -- μ-pos {suc n} U (nd src tgt flr brs) (nd-there p q) r =
  --   γ-inr U flr (μ-brs U brs) p (μ-pos U (br (brs ⊛ p)) q r)

  -- μ-fst {zero} P s p = tt*
  -- μ-fst {suc n} U (nd src tgt flr brs) =
  --   γ-pos-elim U flr (μ-brs U brs) _ (λ _ → nd-here)
  --     (λ p q → nd-there p (μ-fst U (br (brs ⊛ p)) q))

  -- μ-snd {zero} P s p = tt*
  -- μ-snd {suc n} U (nd src tgt flr brs) = 
  --   γ-pos-elim U flr (μ-brs U brs) _ (λ p → p)
  --     (λ p q → μ-snd U (br (brs ⊛ p)) q)
      
