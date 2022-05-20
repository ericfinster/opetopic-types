{-# OPTIONS --no-positivity-check #-}
--
--  OpetopicType.agda - Opetopic Types
--

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat 
open import Cubical.Data.Sum

open import Core.Prelude

module Experimental.Positionless where

  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)

  Frm : ∀ {n ℓ} → 𝕆Type n ℓ → Type ℓ
  
  Src : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → Frm X → Type ℓ 

  {-# TERMINATING #-}
  Pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → Type ℓ 

  Typ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (p : Pos P s) → Frm X 

  _⊚_ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (p : Pos P s)
    → P (Typ s p)

  η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → {f : Frm X} (x : P f)
    → Src P f 

  η-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → {f : Frm X} (x : P f)
    → Pos P (η x)

  μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P Q : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Src Q (Typ s p))
    → Src Q f 

  μ-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P Q : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Src Q (Typ s p))
    → (p : Pos P s)
    → (q : Pos Q (ϕ p))
    → Pos Q (μ s ϕ) 
    
  μ-fst : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P Q : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Src Q (Typ s p))
    → (p : Pos Q (μ s ϕ))
    → Pos P s  

  μ-snd : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P Q : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Src Q (Typ s p))
    → (p : Pos Q (μ s ϕ))
    → Pos Q (ϕ (μ-fst s ϕ p))

  postulate

    -- Typing and Inhabitants of μ and η
    Typ-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (p : Pos P (η x))
      → Typ (η x) p ↦ f
    {-# REWRITE Typ-η #-}

    ⊚-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (p : Pos P (η x))
      → η x ⊚ p ↦ x
    {-# REWRITE ⊚-η #-}

    Typ-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos Q (μ s ϕ))
      → Typ (μ s ϕ) p ↦ Typ (ϕ (μ-fst s ϕ p)) (μ-snd s ϕ p)
    {-# REWRITE Typ-μ #-}

    ⊚-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos Q (μ s ϕ))
      → μ s ϕ ⊚ p ↦ ϕ (μ-fst s ϕ p) ⊚ μ-snd s ϕ p
    {-# REWRITE ⊚-μ #-}

    -- Laws for positions
    μ-fst-β : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → μ-fst s ϕ (μ-pos s ϕ p q) ↦ p 
    {-# REWRITE μ-fst-β #-}

    μ-snd-β : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → μ-snd s ϕ (μ-pos s ϕ p q) ↦ q
    {-# REWRITE μ-snd-β #-}

    -- Monad Laws
    unit-left : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P Q : Frm X → Type ℓ)
      → (f : Frm X) (x : P f)
      → (ϕ : (p : Pos P (η x)) → Src Q f)
      → μ (η x) ϕ ↦ ϕ (η-pos x)
    {-# REWRITE unit-left #-}
    
    unit-right : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ s (λ p → η (s ⊚ p)) ↦ s
    {-# REWRITE unit-right #-}
    
    μ-assoc : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P Q R : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (ψ : (pq : Pos Q (μ s ϕ)) → Src R (Typ (μ s ϕ) pq))
      → μ (μ s ϕ) ψ ↦ μ s (λ p → μ (ϕ p) (λ q → ψ (μ-pos s ϕ p q)))
    {-# REWRITE μ-assoc #-}

  𝕆Type zero ℓ = Lift Unit
  𝕆Type (suc n) ℓ =
    Σ[ X ∈ 𝕆Type n ℓ ]
    ((f : Frm X) → Type ℓ)

  Frm {zero} X = Lift Unit
  Frm {suc n} (X , P) = 
    Σ[ f ∈ Frm X ]
    Σ[ tgt ∈ P f ] 
    Src P f

  module _ {n ℓ} {X : 𝕆Type n ℓ} {P : Frm X → Type ℓ}
           (U : Frm (X , P) → Type ℓ) where

    data Pd : Frm (X , P) → Type ℓ

    record Branch (f : Frm X) : Type ℓ where
      inductive
      eta-equality
      constructor [_,_,_]
      field
        stm : P f
        lvs : Src P f
        br : Pd (f , stm , lvs)

    open Branch public
    
    data Pd where

      lf : {f : Frm X} (tgt : P f)
         → Pd (f , tgt , η tgt) 

      nd : {f : Frm X} (tgt : P f)
         → (brs : Src Branch f)
         → (flr : U (f , tgt , μ brs (λ p → η (stm (brs ⊚ p)))))
         → Pd (f , tgt , μ brs (λ p → lvs (brs ⊚ p)))

  Src {zero} P _ = P tt*
  Src {suc n} U = Pd U

  Pos {zero} P s = Lift Unit
  Pos {suc n} U (lf tgt) = Lift ⊥
  Pos {suc n} U (nd tgt brs flr) =
    Unit ⊎ (Σ[ p ∈ Pos (Branch U) brs ]
            Pos U (br (brs ⊚ p)))

  Typ {zero} s p = tt*
  Typ {suc n} {X = X , P} {P = U} (nd tgt brs flr) (inl _) =
    _ , tgt , μ {Q = P} brs (λ p → η {P = P} (stm (brs ⊚ p)))
  Typ {suc n} (nd tgt brs flr) (inr (p , q)) = Typ (br (brs ⊚ p)) q

  _⊚_ = {!!} 

  -- Inhab {zero} Xₙ Xₛₙ s p = s
  -- Inhab {suc n} (Xₙ , Xₛₙ) Xₛₛₙ ._ (nd-here {flr = flr}) = flr
  -- Inhab {suc n} (Xₙ , Xₛₙ) Xₛₛₙ ._ (nd-there {brs = brs} p q) = 
  --   Inhab (Xₙ , Xₛₙ) Xₛₛₙ (br (Inhab Xₙ (Branch Xₙ Xₛₙ Xₛₛₙ) brs p)) q 


  η = {!!} 
  η-pos = {!!}

  μ = {!!} 
  μ-pos = {!!} 
  μ-fst = {!!} 
  μ-snd = {!!} 

  -- η {zero} Xₙ Xₛₙ x = x
  -- η {suc n} (Xₙ , Xₛₙ) Xₛₛₙ {f , t , s} x =
  --   let brs = μ Xₙ Xₛₙ (Branch Xₙ Xₛₙ Xₛₛₙ) s (λ _ p → η Xₙ (Branch Xₙ Xₛₙ Xₛₛₙ) [ Inhab Xₙ Xₛₙ s p , _ , lf (Inhab Xₙ Xₛₙ s p) ])
  --   in nd t brs x 
  
  -- η-pos {zero} Xₙ Xₛₙ x = tt*
  -- η-pos {suc n} Xₙ Xₛₙ x = nd-here

  -- -- graft : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ) (Xₛₙ : Frm Xₙ → Type ℓ)
  -- --   → (Xₛₛₙ : Frm (Xₙ , Xₛₙ) → Type ℓ)
  -- --   → (f : Frm Xₙ) (tgt : Xₛₙ f)
  -- --   → (src : Src Xₙ Xₛₙ f) (ϕ : (f' : Frm Xₙ) (p : Pos Xₙ Xₛₙ src f) → Branch Xₙ Xₛₙ Xₛₛₙ f)
  -- --   → (pd : Pd Xₙ Xₛₙ Xₛₛₙ (f , tgt , src))
  -- --   → Pd Xₙ Xₛₙ Xₛₛₙ (f , tgt , μ Xₙ Xₛₙ {!!})
  -- -- graft = {!!} 
  
  -- -- γ : ∀ {n ℓ} (Xₙ : 𝕆Type n ℓ) (Xₛₙ : Frm Xₙ → Type ℓ)
  -- --   → (Xₛₛₙ : Frm (Xₙ , Xₛₙ) → Type ℓ)
  -- --   → (f : Frm Xₙ) (tgt : Xₛₙ f)
  -- --   → (ih : Src Xₙ (Branch Xₙ Xₛₙ Xₛₛₙ) f)
  -- --   → Pd Xₙ Xₛₙ Xₛₛₙ (f , tgt , smap Xₙ (λ _ → stm) ih)
  -- --   → Pd Xₙ Xₛₙ Xₛₛₙ (f , tgt , μ Xₙ Xₛₙ (smap Xₙ (λ _ → lvs) ih))

  -- μ = {!!} 
  -- -- μ {zero} Xₙ Xₛₙ pd = pd
  -- -- μ {suc n} Xₙ Xₛₙ (lf tgt) = lf tgt
  -- -- μ {suc n} (Xₙ , Xₛₙ) Xₛₛₙ (nd f tgt ih filler) =
  -- --   let ih' = smap Xₙ (λ f br → [ stm br , lvs br , μ (Xₙ , Xₛₙ) Xₛₛₙ (br br) ]) ih  
  -- --   in γ Xₙ Xₛₙ Xₛₛₙ f tgt ih' filler
