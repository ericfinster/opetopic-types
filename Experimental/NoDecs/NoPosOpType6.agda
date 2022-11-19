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

module Experimental.NoDecs.NoPosOpType6 where

  --
  --  Opetopic Types
  --

  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)
  Frm : ∀ {n ℓ} → 𝕆Type n ℓ → Type ℓ

  postulate

    Src : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → Frm X → Type ℓ

    Dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : {f : Frm X} → P f → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → Type ℓ 

    split-fst : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {R : {f : Frm X} → Q f → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : {f : Frm X} → P f → Q f)
      → (ψ : {f : Frm X} (p : P f) → R (ϕ p))
      → Src Q f

    split-snd : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {R : {f : Frm X} → Q f → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : {f : Frm X} → P f → Q f)
      → (ψ : {f : Frm X} (p : P f) → R (ϕ p))
      → Dec R (split-fst {R = R} s ϕ ψ)

    merge : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {R : {f : Frm X} → P f → Type ℓ}
      → {f : Frm X} (s : Src P f) (δ : Dec R s)
      → (ϕ : {f : Frm X} (p : P f) (r : R p) → Q f)
      → Src Q f

  ν : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P Q : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (σ : {f : Frm X} → P f → Q f)
    → Src Q f
  ν s σ = merge (split-fst s σ (λ _ → tt*))
                (split-snd s σ (λ _ → tt*))
                (λ q _ → q)

  -- But there's also this:
  ν' : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P Q : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (σ : {f : Frm X} → P f → Q f)
    → Src Q f
  ν' {P = P} {Q} s σ =
    merge {P = P} {Q = Q} {R = const Unit*}
      (split-fst s (λ p → p) (λ _ → tt*))
      (split-snd s (λ p → p) (λ _ → tt*))
       (λ p _ → σ p)
  
  postulate
  
    -- 
    --  Monadic Structure
    --

    η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (x : P f)
      → Src P f 

    μ : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f) → Src P f 

    --
    --  Decomposing Decorations
    --

    η-dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : {f : Frm X} → P f → Type ℓ}
      → {f : Frm X} (x : P f)
      → Dec Q (η P x) → Q x
  
    μ-dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : {f : Frm X} → P f → Type ℓ}
      → {f : Frm X} (s : Src (Src P) f)
      → Dec Q (μ P s) → Dec (Dec Q) s 

    --
    --  Monad Laws
    --

    μ-unit-l : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ P (η (Src P) s) ↦ s 
    {-# REWRITE μ-unit-l #-}

    -- μ-unit-r : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    --   → (P : Frm X → Type ℓ)
    --   → (f : Frm X) (s : Src P f)
    --   → μ P (ν (η P) s) ↦ s
    -- {-# REWRITE μ-unit-r #-}

    -- μ-assoc : ∀ {n ℓ} (X : 𝕆Type n ℓ)
    --   → (P : Frm X → Type ℓ)
    --   → (f : Frm X) (s : Src (Src (Src P)) f)
    --   → μ P (μ (Src P) s) ↦ μ P (ν (μ P) s) 
    -- {-# REWRITE μ-assoc #-}

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

    record Branch {f : Frm X} (x : P f) : Type ℓ where
      inductive
      eta-equality
      constructor [_,_,_]
      field
        lvs : Src P f
        br : Pd (f , lvs , x)

    open Branch public
    
    data Pd where

      lf : {f : Frm X} (tgt : P f)
         → Pd (f , η P tgt , tgt) 

      nd : {f : Frm X} (src : Src P f) (tgt : P f)
         → (flr : U (f , src , tgt))
         → (brs : Dec Branch src) 
         → Pd (f , μ P (merge src brs (λ _ → lvs)) , tgt)

    -- γ : {frm : Frm X} {src : Src P frm} {tgt : P frm}
    --   → (pd : Pd (frm , src , tgt ))
    --   → (brs : Dec Branch src)
    --   → Pd (frm , {!!} , tgt)
    -- γ (lf tgt) brs = {!!}
    -- γ (nd src tgt flr lbrs) brs = {!!}


