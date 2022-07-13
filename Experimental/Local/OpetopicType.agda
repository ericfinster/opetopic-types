{-# OPTIONS --no-positivity-check --no-termination-check #-}
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

module Experimental.Local.OpetopicType where

  --
  --  Opetopic Types
  --

  -- infixl 50 _⊙_

  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)
  Frm : ∀ {n ℓ} → 𝕆Type n ℓ → Type ℓ

  postulate

    Src : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → Frm X → Type ℓ

    Pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → Type ℓ 

    Typ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (p : Pos P s) → Frm X 

    _⊚_ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (p : Pos P s)
      → P (Typ P s p)

    --
    --  Monadic Structure
    --

    ν : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → Src Q f

    η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (x : P f)
      → Src P f 

    μ : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f) → Src P f 

    --
    --  Position Intro 
    --

    ν-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → Pos P s → Pos Q (ν s ϕ)

    η-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (x : P f)
      → Pos P (η P x)

    μ-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (p : Pos (Src P) s)
      → (q : Pos P (s ⊚ p))
      → Pos P (μ P s)

    --
    --  Position Elim
    --

    ν-lift : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → Pos Q (ν s ϕ) → Pos P s
      
    η-pos-elim : ∀ {n ℓ ℓ'} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (Q : Pos P (η P x) → Type ℓ')
      → (q : Q (η-pos P x))
      → (p : Pos P (η P x)) → Q p

    μ-fst : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (p : Pos P (μ P s))
      → Pos (Src P) s

    μ-snd : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (p : Pos P (μ P s))
      → Pos P (s ⊚ μ-fst P s p)

    --
    --  Decorations
    --
    
    Dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : {f : Frm X} → P f → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → Type ℓ 

    _⊛_ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : {f : Frm X} → P f → Type ℓ}
      → {f : Frm X} {s : Src P f} (δ : Dec Q s)
      → (p : Pos P s) → Q (s ⊚ p) 

    λ-dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : {f : Frm X} → P f → Type ℓ)
      → {f : Frm X} (s : Src P f) 
      → (δ : (p : Pos P s) → Q (s ⊚ p))
      → Dec Q s 

    λ-dec-β : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : {f : Frm X} → P f → Type ℓ)
      → {f : Frm X} (s : Src P f) 
      → (δ : (p : Pos P s) → Q (s ⊚ p))
      → (p : Pos P s)
      → λ-dec Q s δ ⊛ p ↦ δ p
    {-# REWRITE λ-dec-β #-} 

    --
    --  Position Computation
    --

    ν-lift-β : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (p : Pos P s)
      → ν-lift {Q = Q} s ϕ (ν-pos s ϕ p) ↦ p
    {-# REWRITE ν-lift-β #-} 

    μ-fst-β : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (p : Pos (Src P) s)
      → (q : Pos P (s ⊚ p))
      → μ-fst P s (μ-pos P s p q) ↦ p
    {-# REWRITE μ-fst-β #-}

    μ-snd-β : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (p : Pos (Src P) s)
      → (q : Pos P (s ⊚ p))
      → μ-snd P s (μ-pos P s p q) ↦ q
    {-# REWRITE μ-snd-β #-}

    --
    --  Typing and Inhabitants
    --

    Typ-ν : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (p : Pos Q (ν s ϕ))
      → Typ Q (ν s ϕ) p ↦ Typ P s (ν-lift s ϕ p)
    {-# REWRITE Typ-ν #-}

    ⊚-ν : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (p : Pos Q (ν s ϕ))
      → ν s ϕ ⊚ p ↦ ϕ (ν-lift s ϕ p)
    {-# REWRITE ⊚-ν #-}

    Typ-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (p : Pos P (η P x))
      → Typ P (η P x) p ↦ f
    {-# REWRITE Typ-η #-}

    ⊚-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (p : Pos P (η P x))
      → η P x ⊚ p ↦ x
    {-# REWRITE ⊚-η #-}

    Typ-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (p : Pos P (μ P s))
      → Typ P (μ P s) p ↦ Typ P (s ⊚ μ-fst P s p) (μ-snd P s p)
    {-# REWRITE Typ-μ #-}

    ⊚-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (p : Pos P (μ P s))
      → μ P s ⊚ p ↦ (s ⊚ (μ-fst P s p)) ⊚ (μ-snd P s p)
    {-# REWRITE ⊚-μ #-}

    -- 
    -- Naturality Laws
    --

    ν-ν : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P Q R : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (ψ : (p : Pos Q (ν s ϕ)) → R (Typ Q (ν s ϕ) p))
      → ν {Q = R} (ν s ϕ) ψ ↦ ν s (λ p → ψ (ν-pos s ϕ p))
    {-# REWRITE ν-ν #-} 
      
    ν-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P Q : Frm X → Type ℓ)
      → {f : Frm X} (x : P f)
      → (ϕ : (p : Pos P (η P x)) → Q f)
      → ν (η P x) ϕ ↦ η Q (ϕ (η-pos P x))
    {-# REWRITE ν-η #-}

    ν-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P Q : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (ϕ : (p : Pos P (μ P s)) → Q (Typ P (μ P s) p))
      → ν (μ P s) ϕ ↦ μ Q (ν s (λ p → ν (s ⊚ p) (λ q → ϕ (μ-pos P s p q))))
    {-# REWRITE ν-μ #-}

    --
    -- Monad Laws
    --

    μ-unit-l : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ P (η (Src P) s) ↦ s 
    {-# REWRITE μ-unit-l #-}

    μ-unit-r : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ P (ν s (λ p → η P (s ⊚ p))) ↦ s
    {-# REWRITE μ-unit-r #-}

    μ-assoc : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src (Src (Src P)) f)
      → μ P (μ (Src P) s) ↦ μ P (ν s (λ p → μ P (s ⊚ p))) 
    {-# REWRITE μ-assoc #-}

  --
  --  Definitions of opeotpic types and frames
  --

  𝕆Type zero ℓ = Lift Unit
  𝕆Type (suc n) ℓ =
    Σ[ X ∈ 𝕆Type n ℓ ]
    ((f : Frm X) → Type ℓ)

  Frm {zero} X = Lift Unit
  Frm {suc n} (X , P) = 
    Σ[ f ∈ Frm X ]
    Σ[ src ∈ Src P f ] 
    P f

  --
  --  Pasting Diagrams and their Positions 
  --

  module _ {n ℓ} {X : 𝕆Type n ℓ} {P : Frm X → Type ℓ} (U : Frm (X , P) → Type ℓ) where

    data Pd : Frm (X , P) → Type ℓ

    record Branch {f : Frm X} (stm : P f) : Type ℓ where
      inductive
      eta-equality
      constructor [_,_]
      field
        lvs : Src P f
        br : Pd (f , lvs , stm)

    open Branch public

    -- Note: this could be more general as P is not used ...
    canopy : {f : Frm X} {s : Src P f}
      → Dec Branch s → Src P f
    canopy {s = s} δ = μ P (ν s (λ p → lvs (δ ⊛ p)))

    canopy-pos : {f : Frm X} {s : Src P f}
      → (brs : Dec Branch s)
      → (p : Pos P s) (q : Pos P (lvs (brs ⊛ p)))
      → Pos P (canopy brs) 
    canopy-pos {s = s} brs p q =
      μ-pos P (ν s (λ q → lvs (brs ⊛ q)))
        (ν-pos s (λ q → lvs (brs ⊛ q)) p) q

    canopy-fst : {f : Frm X} {s : Src P f}
      → (brs : Dec Branch s) (p : Pos P (canopy brs))
      → Pos P s 
    canopy-fst {s = s} brs p =
      ν-lift s (λ p → lvs (brs ⊛ p))
        (μ-fst P (ν s (λ p → lvs (brs ⊛ p))) p)  

    canopy-snd : {f : Frm X} {s : Src P f}
      → (brs : Dec Branch s) (p : Pos P (canopy brs))
      → Pos P (lvs (brs ⊛ canopy-fst brs p))
    canopy-snd {s = s} brs p = μ-snd P (ν s (λ p → lvs (brs ⊛ p))) p

    data Pd where

      lf : {f : Frm X} (tgt : P f)
         → Pd (f , η P tgt , tgt) 

      nd : {f : Frm X} (src : Src P f) (tgt : P f) 
         → (flr : U (f , src , tgt))
         → (brs : Dec Branch src)
         → Pd (f , μ P (ν src (λ p → lvs (brs ⊛ p))) , tgt)

    γ : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (brs : (p : Pos P src) → Branch (src ⊚ p))
      → Pd (frm , μ P (ν src λ p → lvs (brs p)) , tgt)

    γ-brs : {frm : Frm X} {src : Src P frm} (lbrs : Dec Branch src)
      → (brs : (p : Pos P (canopy lbrs)) → Branch (canopy lbrs ⊚ p))
      → (p : Pos P src) → Branch (src ⊚ p)
    γ-brs lbrs brs p = [ μ P (ν (lvs (lbrs ⊛ p)) (λ q → lvs (brs (canopy-pos lbrs p q))))
                       , γ (br (lbrs ⊛ p)) (λ q → brs (canopy-pos lbrs p q))
                       ]

    γ (lf tgt) brs = br (brs (η-pos P tgt))
    γ (nd src tgt flr lbrs) brs =
      nd src tgt flr (λ-dec Branch src (γ-brs lbrs brs))
    

