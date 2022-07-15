{-# OPTIONS --no-positivity-check --no-termination-check --experimental-lossy-unification #-}
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

module Experimental.NoDecs.RevisedOpetopicType where

  --
  --  Opetopic Types
  --

  infixl 50 _⊙_

  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)
  Frm : ∀ {n ℓ} → 𝕆Type n ℓ → Type ℓ

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
  --  Maps of Opetopic Types
  --

  _⇒_ : ∀ {n ℓ₀ ℓ₁} → 𝕆Type n ℓ₀ → 𝕆Type n ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)

  id-map : ∀ {n ℓ} → (X : 𝕆Type n ℓ) → X ⇒ X

  _⊙_ : ∀ {n ℓ₀ ℓ₁ ℓ₂} {X : 𝕆Type n ℓ₀}
    → {Y : 𝕆Type n ℓ₁} {Z : 𝕆Type n ℓ₂}
    → Y ⇒ Z → X ⇒ Y → X ⇒ Z

  Frm⇒ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → (σ : X ⇒ Y) → Frm X → Frm Y

  postulate
  
    --
    --  Equations for maps
    -- 

    Frm⇒-id : ∀ {n ℓ} (X : 𝕆Type n ℓ) (f : Frm X)
      → Frm⇒ (id-map X) f ↦ f
    {-# REWRITE Frm⇒-id #-}

    Frm⇒-⊙ : ∀ {n ℓ₀ ℓ₁ ℓ₂} {X : 𝕆Type n ℓ₀}
      → {Y : 𝕆Type n ℓ₁} {Z : 𝕆Type n ℓ₂}
      → (σ : X ⇒ Y) (τ : Y ⇒ Z) (f : Frm X)
      → Frm⇒ τ (Frm⇒ σ f) ↦ Frm⇒ (τ ⊙ σ) f 
    {-# REWRITE Frm⇒-⊙ #-}

    map-unit-l : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → (σ : X ⇒ Y)
      → id-map Y ⊙ σ ↦ σ
    {-# REWRITE map-unit-l #-}

    map-unit-r : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → (σ : X ⇒ Y)
      → σ ⊙ id-map X ↦ σ
    {-# REWRITE map-unit-r #-}

    map-assoc : ∀ {n ℓ₀ ℓ₁ ℓ₂ ℓ₃} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {Z : 𝕆Type n ℓ₂} {W : 𝕆Type n ℓ₃}
      → (ρ : X ⇒ Y) (σ : Y ⇒ Z) (τ : Z ⇒ W)
      → τ ⊙ (σ ⊙ ρ) ↦ τ ⊙ σ ⊙ ρ
    {-# REWRITE map-assoc #-} 

  --
  --  Monadic Structure
  --

  ν : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → {P : Frm X → Type ℓ₀}
    → {Q : Frm Y → Type ℓ₁}
    → {f : Frm X} (s : Src P f)
    → (σ : X ⇒ Y)
    → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
    → Src Q (Frm⇒ σ f)

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

  ν-pos : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → {P : Frm X → Type ℓ₀}
    → {Q : Frm Y → Type ℓ₁}
    → {f : Frm X} (s : Src P f)
    → (σ : X ⇒ Y)
    → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
    → Pos P s → Pos Q (ν s σ ϕ)

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

  ν-lift : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → {P : Frm X → Type ℓ₀}
    → {Q : Frm Y → Type ℓ₁}
    → {f : Frm X} (s : Src P f)
    → (σ : X ⇒ Y)
    → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
    → Pos Q (ν s σ ϕ) → Pos P s
      
  η-pos-elim : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀}
    → {P : Frm X → Type ℓ₀}
    → {f : Frm X} (x : P f)
    → (Q : Pos P (η P x) → Type ℓ₁)
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

  postulate
  
    --
    --  Position Computation
    --

    ν-lift-β : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {f : Frm X} (s : Src P f)
      → (σ : X ⇒ Y)
      → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos P s)
      → ν-lift {Q = Q} s σ ϕ (ν-pos s σ ϕ p) ↦ p
    {-# REWRITE ν-lift-β #-} 

    ν-lift-η : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {f : Frm X} (s : Src P f)
      → (σ : X ⇒ Y)
      → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (ν s σ ϕ))
      → ν-pos {Q = Q} s σ ϕ (ν-lift s σ ϕ p) ↦ p
    {-# REWRITE ν-lift-η #-} 

    η-pos-elim-β : ∀ {n ℓ ℓ'} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (Q : Pos P (η P x) → Type ℓ')
      → (q : Q (η-pos P x))
      → η-pos-elim x Q q (η-pos P x) ↦ q
    {-# REWRITE η-pos-elim-β #-}

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

    μ-pos-η : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f)
      → (p : Pos P (μ P s))
      → μ-pos P s (μ-fst P s p) (μ-snd P s p) ↦ p
    {-# REWRITE μ-pos-η #-}

    --
    --  Typing and Inhabitants
    --

    Typ-ν : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {f : Frm X} (s : Src P f)
      → (σ : X ⇒ Y)
      → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (ν s σ ϕ))
      → Typ Q (ν s σ ϕ) p ↦ Frm⇒ σ (Typ P s (ν-lift s σ ϕ p))
    {-# REWRITE Typ-ν #-}

    -- BUG: Extra id rewrite!
    Typ-ν-id : ∀ {n ℓ₀} {X : 𝕆Type n ℓ₀} 
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm X → Type ℓ₀}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (p : Pos Q (ν s (id-map X) ϕ))
      → Typ Q (ν s (id-map X) ϕ) p ↦ Typ P s (ν-lift s (id-map X) ϕ p)
    {-# REWRITE Typ-ν-id #-}

    ⊚-ν : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {f : Frm X} (s : Src P f)
      → (σ : X ⇒ Y)
      → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (ν s σ ϕ))
      → ν s σ ϕ ⊚ p ↦ ϕ (ν-lift s σ ϕ p)
    {-# REWRITE ⊚-ν #-}

    -- BUG: Extra id rewrite!
    ⊚-ν-id : ∀ {n ℓ₀} {X : 𝕆Type n ℓ₀}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm X → Type ℓ₀}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (p : Pos Q (ν s (id-map X) ϕ))
      → ν s (id-map X) ϕ ⊚ p ↦ ϕ (ν-lift s (id-map X) ϕ p)
    {-# REWRITE ⊚-ν-id #-}

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

    ν-id : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → ν s (id-map X) (λ p → s ⊚ p) ↦ s
    {-# REWRITE ν-id #-}
    
    ν-ν : ∀ {n ℓ₀ ℓ₁ ℓ₂} {X : 𝕆Type n ℓ₀}
      → {Y : 𝕆Type n ℓ₁} {Z : 𝕆Type n ℓ₂}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {R : Frm Z → Type ℓ₂}
      → {f : Frm X} (s : Src P f)
      → (σ : X ⇒ Y) (τ : Y ⇒ Z)
      → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (ψ : (q : Pos Q (ν s σ ϕ)) → R (Frm⇒ τ (Typ Q (ν s σ ϕ) q)))
      → ν {Q = R} (ν s σ ϕ) τ ψ ↦ ν s (τ ⊙ σ) (λ p → ψ (ν-pos s σ ϕ p))
    {-# REWRITE ν-ν #-}

    -- BUG: Extra id rewrite!
    ν-ν-id : ∀ {n ℓ₀ ℓ₂} {X : 𝕆Type n ℓ₀}
      → {Z : 𝕆Type n ℓ₂}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm X → Type ℓ₀}
      → {R : Frm Z → Type ℓ₂}
      → {f : Frm X} (s : Src P f)
      → (τ : X ⇒ Z)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (ψ : (q : Pos Q (ν s (id-map X) ϕ)) → R (Frm⇒ τ (Typ Q (ν s (id-map X) ϕ) q)))
      → ν {Q = R} (ν s (id-map X) ϕ) τ ψ ↦ ν s τ (λ p → ψ (ν-pos s (id-map X) ϕ p))
    {-# REWRITE ν-ν-id #-}

    ν-η : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {f : Frm X} (x : P f)
      → (σ : X ⇒ Y)
      → (ϕ : (p : Pos P (η P x)) → Q (Frm⇒ σ f))
      → ν (η P x) σ ϕ ↦ η Q (ϕ (η-pos P x))
    {-# REWRITE ν-η #-}

    ν-μ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {f : Frm X} (s : Src (Src P) f)
      → (σ : X ⇒ Y)
      → (ϕ : (p : Pos P (μ P s)) → Q (Frm⇒ σ (Typ P (μ P s) p)))
      → ν (μ P s) σ ϕ ↦ μ Q (ν s σ (λ p → ν (s ⊚ p) σ (λ q → ϕ (μ-pos P s p q))))
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
      → μ P (ν s (id-map X) (λ p → η P (s ⊚ p))) ↦ s
    {-# REWRITE μ-unit-r #-}

    μ-assoc : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src (Src (Src P)) f)
      → μ P (μ (Src P) s) ↦ μ P (ν s (id-map X) (λ p → μ P (s ⊚ p))) 
    {-# REWRITE μ-assoc #-}

    -- INCOMPLETE : there are the compatibilities of into/elims with the laws for ν , μ and η

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

    record Branch (f : Frm X) : Type ℓ where
      inductive
      eta-equality
      constructor [_,_,_]
      field
        stm : P f
        lvs : Src P f
        br : Pd (f , lvs , stm)

    open Branch public

    understory : {f : Frm X} → Src Branch f → Src P f
    understory brs = ν brs (id-map X) (λ p → stm (brs ⊚ p))

    understory-pos : {f : Frm X} (brs : Src Branch f)
      → Pos Branch brs → Pos P (understory brs) 
    understory-pos brs = ν-pos brs (id-map X) (λ p → stm (brs ⊚ p))

    understory-lift : {f : Frm X} (brs : Src Branch f)
      → Pos P (understory brs) → Pos Branch brs
    understory-lift brs = ν-lift brs (id-map X) (λ p → stm (brs ⊚ p))

    canopy : {f : Frm X} → Src Branch f → Src P f
    canopy brs = μ P (ν brs (id-map X) (λ p → lvs (brs ⊚ p)))

    canopy-pos : {f : Frm X} (brs : Src Branch f)
      → (p : Pos Branch brs) (q : Pos P (lvs (brs ⊚ p)))
      → Pos P (canopy brs) 
    canopy-pos brs p q =
      μ-pos P (ν brs (id-map X) (λ r → lvs (brs ⊚ r)))
        (ν-pos brs (id-map X) (λ r → lvs (brs ⊚ r)) p) q 

    canopy-fst : {f : Frm X} (brs : Src Branch f)
      → Pos P (canopy brs) → Pos Branch brs
    canopy-fst brs p = ν-lift brs (id-map X) (λ r → lvs (brs ⊚ r))
      (μ-fst P (ν brs (id-map X) (λ p → lvs (brs ⊚ p))) p) 

    canopy-snd : {f : Frm X} (brs : Src Branch f)
      → (p : Pos P (canopy brs)) → Pos P (lvs (brs ⊚ canopy-fst brs p))
    canopy-snd brs p = μ-snd P (ν brs (id-map X) (λ p → lvs (brs ⊚ p))) p

    Branch' : {f : Frm X} → P f → Type ℓ
    Branch' {f} tgt = Σ[ cn ∈ Src P f ] Pd (f , cn , tgt)

    data Pd where

      lf : {f : Frm X} (tgt : P f)
         → Pd (f , η P tgt , tgt) 

      nd : {f : Frm X} (tgt : P f)
         → (brs : Src Branch f)
         → (flr : U (f , understory brs , tgt))
         → Pd (f , canopy brs , tgt)

    data PdPos : {f : Frm (X , P)} → Pd f → Type ℓ where

      nd-here : {f : Frm X} {tgt : P f}
         → {brs : Src Branch f}
         → {flr : U (f , understory brs , tgt)}
         → PdPos (nd tgt brs flr)

      nd-there : {f : Frm X} {tgt : P f}
         → {brs : Src Branch f}
         → {flr : U (f , understory brs , tgt)}
         → (p : Pos Branch brs) (q : PdPos (br (brs ⊚ p)))
         → PdPos (nd tgt brs flr)


    γ : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (ϕ : (p : Pos P src) → Branch' (src ⊚ p))
      → Pd (frm , μ P (ν src (id-map X) (λ p → fst (ϕ p))) , tgt)

    γ-brs : {frm : Frm X} (brs : Src Branch frm)
      → (ϕ : (p : Pos P (canopy brs)) → Branch' (canopy brs ⊚ p))
      → (p : Pos Branch brs) → Branch (Typ Branch brs p)
    γ-brs brs ϕ p = [ stm (brs ⊚ p) , _ , γ (br (brs ⊚ p)) (λ q → ϕ (canopy-pos brs p q)) ]

    γ (lf tgt) ϕ = snd (ϕ (η-pos P tgt))
    γ (nd tgt brs flr) ϕ = nd tgt (ν brs (id-map X) (γ-brs brs ϕ)) flr

    γ-inl : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (ϕ : (p : Pos P src) → Branch' (src ⊚ p))
      → (p : PdPos pd) → PdPos (γ pd ϕ)
    γ-inl (nd tgt brs flr) ϕ nd-here = nd-here
    γ-inl (nd tgt brs flr) ϕ (nd-there p q) =
      nd-there (ν-pos brs (id-map X) (γ-brs brs ϕ) p)
               (γ-inl (br (brs ⊚ p)) (ϕ ∘ canopy-pos brs p) q)

    γ-inr : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (ϕ : (p : Pos P src) → Branch' (src ⊚ p))
      → (p : Pos P src) (q : PdPos (snd (ϕ p)))
      → PdPos (γ pd ϕ)
    γ-inr (lf tgt) ϕ p q =
      η-pos-elim tgt (λ p → PdPos (snd (ϕ p)) → PdPos (snd (ϕ (η-pos P tgt)))) (λ x → x) p q
    γ-inr (nd tgt brs flr) ϕ pq r =
      let p = canopy-fst brs pq
          q = canopy-snd brs pq 
      in nd-there (ν-pos brs (id-map X) (γ-brs brs ϕ) p)
                  (γ-inr (br (brs ⊚ p)) (ϕ ∘ canopy-pos brs p) q r) 

    γ-pos-elim : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (ϕ : (p : Pos P src) → Branch' (src ⊚ p))
      → ∀ {ℓ'} (B : PdPos (γ pd ϕ) → Type ℓ')
      → (inl* : (p : PdPos pd) → B (γ-inl pd ϕ p))
      → (inr* : (p : Pos P src) (q : PdPos (snd (ϕ p))) → B (γ-inr pd ϕ p q))
      → (p : PdPos (γ pd ϕ)) → B p
    γ-pos-elim (lf tgt) ϕ B inl* inr* p = inr* (η-pos P tgt) p
    γ-pos-elim (nd tgt brs flr) ϕ B inl* inr* nd-here = inl* nd-here
    γ-pos-elim (nd tgt brs flr) ϕ B inl* inr* (nd-there u v) =
      let u' = ν-lift brs (id-map X) (γ-brs brs ϕ) u
      in γ-pos-elim (br (brs ⊚ u')) (λ q → ϕ (canopy-pos brs u' q))
           (λ v' → B (nd-there u v')) (λ q → inl* (nd-there u' q))
           (λ q → inr* (canopy-pos brs u' q)) v
           
    postulate
    
      γ-pos-elim-inl-β : {frm : Frm X} {src : Src P frm} {tgt : P frm}
        → (pd : Pd (frm , src , tgt ))
        → (ϕ : (p : Pos P src) → Branch' (src ⊚ p))
        → ∀ {ℓ'} (B : PdPos (γ pd ϕ) → Type ℓ')
        → (inl* : (p : PdPos pd) → B (γ-inl pd ϕ p))
        → (inr* : (p : Pos P src) (q : PdPos (snd (ϕ p))) → B (γ-inr pd ϕ p q))
        → (p : PdPos pd)
        → γ-pos-elim pd ϕ B inl* inr* (γ-inl pd ϕ p) ↦ inl* p
      {-# REWRITE γ-pos-elim-inl-β #-}
        
      γ-pos-elim-inr-β : {frm : Frm X} {src : Src P frm} {tgt : P frm}
        → (pd : Pd (frm , src , tgt ))
        → (ϕ : (p : Pos P src) → Branch' (src ⊚ p))
        → ∀ {ℓ'} (B : PdPos (γ pd ϕ) → Type ℓ')
        → (inl* : (p : PdPos pd) → B (γ-inl pd ϕ p))
        → (inr* : (p : Pos P src) (q : PdPos (snd (ϕ p))) → B (γ-inr pd ϕ p q))
        → (p : Pos P src) (q : PdPos (snd (ϕ p)))
        → γ-pos-elim pd ϕ B inl* inr* (γ-inr pd ϕ p q) ↦ inr* p q
      {-# REWRITE γ-pos-elim-inr-β #-}

  Src {zero} P _ = P tt*
  Src {suc n} U = Pd U

  Pos {zero} P s = Lift Unit
  Pos {suc n} U pd = PdPos U pd

  Typ {zero} P s p = tt*
  Typ {suc n} U (nd tgt brs flr) nd-here = (_ , understory U brs , tgt)
  Typ {suc n} U (nd tgt brs flr) (nd-there p q) = Typ {suc n} U (br (brs ⊚ p)) q

  _⊚_ {zero} s p = s
  _⊚_ {suc n} {P = U} (nd tgt brs flr) nd-here = flr
  _⊚_ {suc n} {P = U} (nd tgt brs flr) (nd-there p q) = _⊚_ (br (brs ⊚ p)) q

  _⇒_ {zero} X Y = Lift Unit
  _⇒_ {suc n} (X , P) (Y , Q) =
    Σ[ σ ∈ X ⇒ Y ]
    ({f : Frm X} → P f → Q (Frm⇒ σ f))

  id-map {zero} X = tt*
  id-map {suc n} (X , P) = id-map X , λ p → p

  _⊙_ {zero} {X = X} {Y} {Z} σ τ = tt*
  _⊙_ {suc n} {X = X , P} {Y , Q} {Z , R} (σₙ , σₛₙ) (τₙ , τₛₙ) =
    σₙ ⊙ τₙ , λ p → σₛₙ (τₛₙ p)

  Frm⇒ {zero} σ f = tt*
  Frm⇒ {suc n} {X = X , P} {Y = Y , Q} (σₙ , σₛₙ) (frm , src , tgt) = 
    Frm⇒ σₙ frm , ν src σₙ (λ p → σₛₙ (src ⊚ p)) , σₛₙ tgt

  ν-brs : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → {P : Frm X → Type ℓ₀} {U : Frm (X , P) → Type ℓ₀}
    → {Q : Frm Y → Type ℓ₁} {V : Frm (Y , Q) → Type ℓ₁}
    → {f : Frm X} {tgt : P f} (brs : Src (Branch U) f)
    → (flr : U (f , understory U brs , tgt))
    → {σ : X ⇒ Y} (σ' : {f : Frm X} → P f → Q (Frm⇒ σ f))
    → (ϕ : (p : PdPos U (nd tgt brs flr)) → V (Frm⇒ (σ , σ') (Typ U (nd tgt brs flr) p)))
    → (p : Pos (Branch U) brs) → Branch V (Frm⇒ σ (Typ (Branch U) brs p))
  ν-brs brs flr {σ = σ} σ' ϕ p =
    [ σ' (stm (brs ⊚ p)) ,
      ν (lvs (brs ⊚ p)) σ (λ q → σ' (lvs (brs ⊚ p) ⊚ q)) ,
      ν (br (brs ⊚ p)) (σ , σ') (λ q → ϕ (nd-there p q)) ]

  ν {zero} s σ ϕ = ϕ tt*
  ν {suc n} (lf tgt) (σ , σ') ϕ = lf (σ' tgt)
  ν {suc n} (nd tgt brs flr) (σ , σ') ϕ =
    nd (σ' tgt) (ν brs σ (ν-brs brs flr σ' ϕ)) (ϕ nd-here)
      
  ν-pos {zero} s σ ϕ p = tt*
  ν-pos {suc n} (nd tgt brs flr) (σ , σ') ϕ nd-here = nd-here
  ν-pos {suc n} (nd tgt brs flr) (σ , σ') ϕ (nd-there p q) =
    nd-there (ν-pos brs σ (ν-brs brs flr σ' ϕ) p)
             (ν-pos (br (brs ⊚ p)) (σ , σ') (λ q' → ϕ (nd-there p q')) q)

  ν-lift {zero} s σ ϕ p = tt*
  ν-lift {suc n} (nd tgt brs flr) (σ , σ') ϕ nd-here = nd-here
  ν-lift {suc n} (nd tgt brs flr) (σ , σ') ϕ (nd-there p q) =
    let p' = ν-lift brs σ (ν-brs brs flr σ' ϕ) p
        q' = ν-lift (br (brs ⊚ p')) (σ , σ') (λ q' → ϕ (nd-there p' q')) q
    in nd-there p' q'

  η {zero} P x = x
  η {suc n} {X = X , P} U {f = frm , src , tgt} x =
    nd tgt (ν src (id-map X) (λ p → [ src ⊚ p , η P (src ⊚ p) , lf (src ⊚ p) ])) x

  η-pos {zero} P x = tt*
  η-pos {suc n} P x = nd-here

  η-pos-elim {zero} x Q q p = q
  η-pos-elim {suc n} x Q q nd-here = q

  μ-brs : ∀ {n ℓ} {X : 𝕆Type n ℓ} {P : Frm X → Type ℓ}
    → (U : Frm (X , P) → Type ℓ)
    → {f : Frm X} (brs : Src (Branch (Pd U)) f)
    → (p : Pos P (understory (Pd U) brs))
    → Branch' U (stm (brs ⊚ understory-lift (Pd U) brs  p))
  μ-brs U brs p = lvs (brs ⊚ understory-lift (Pd U) brs p) ,
                  μ U (br (brs ⊚ understory-lift (Pd U) brs p))
  
  μ {zero} P s = s
  μ {suc n} P (lf tgt) = lf tgt
  μ {suc n} {X = X , P} U (nd tgt brs flr) =
    γ U flr (μ-brs U brs)

  μ-pos {zero} P s p q = tt*
  μ-pos {suc n} U (nd tgt brs flr) nd-here r = 
    γ-inl U flr (μ-brs U brs) r
  μ-pos {suc n} U (nd tgt brs flr) (nd-there p q) r = 
    γ-inr U flr (μ-brs U brs)
      (understory-pos (Pd U) brs p) (μ-pos U (br (brs ⊚ p)) q r)

  μ-fst {zero} P s p = tt*
  μ-fst {suc n} U (nd tgt brs flr) =
    γ-pos-elim U flr (μ-brs U brs) _
      (λ _ → nd-here)
      (λ p q → let p' = understory-lift (Pd U) brs p
               in nd-there p' (μ-fst U (br (brs ⊚ p')) q))

  μ-snd {zero} P s p = tt*
  μ-snd {suc n} U (nd tgt brs flr) = 
    γ-pos-elim U flr (μ-brs U brs) _
      (λ p → p)
      (λ p q → let p' = understory-lift (Pd U) brs p
               in μ-snd U (br (brs ⊚ p')) q)
  
