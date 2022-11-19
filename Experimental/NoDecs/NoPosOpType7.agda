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

module Experimental.NoDecs.NoPosOpType7 where

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

    -- 
    --  Monadic Structure
    --

    ν : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → (σ : {f : Frm X} → P f → Q f)
      → {f : Frm X} (s : Src P f)
      → Src Q f

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

    -- INCOMPLETE : there should be compatibility conditions with the
    -- monad and naturality laws.

    ν-dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {R : {f : Frm X} → Q f → Type ℓ}
      → (σ : {f : Frm X} → P f → Q f)
      → {f : Frm X} (s : Src P f)
      → Dec R (ν σ s) → Dec (λ p → R (σ p)) s 

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
    --  Naturality
    --

    ν-ν : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q R : Frm X → Type ℓ}
      → (σ : {f : Frm X} → P f → Q f)
      → (τ : {f : Frm X} → Q f → R f)
      → {f : Frm X} (s : Src P f)
      → ν τ (ν σ s) ↦ ν (λ p → τ (σ p)) s
    {-# REWRITE ν-ν #-}

    ν-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → (σ : {f : Frm X} → P f → Q f)
      → {f : Frm X} (x : P f)
      → ν σ (η P x) ↦ η Q (σ x) 
    {-# REWRITE ν-η #-}

    ν-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → (σ : {f : Frm X} → P f → Q f)
      → {f : Frm X} (s : Src (Src P) f)
      → ν σ (μ P s) ↦ μ Q (ν (ν σ) s)
    {-# REWRITE ν-μ #-}

    --
    --  Monad Laws
    --

    μ-unit-l : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ P (η (Src P) s) ↦ s 
    {-# REWRITE μ-unit-l #-}

    μ-unit-r : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ P (ν (η P) s) ↦ s
    {-# REWRITE μ-unit-r #-}

    μ-assoc : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src (Src (Src P)) f)
      → μ P (μ (Src P) s) ↦ μ P (ν (μ P) s) 
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

    record Branch {f : Frm X} (x : P f) : Type ℓ where
      inductive
      eta-equality
      constructor [_,_,_]
      field
        lvs : Src P f
        br : Pd (f , lvs , x)

    open Branch public

    canopy : {f : Frm X} (src : Src P f) (brs : Dec Branch src) → Src P f

    canopy-dec : {f : Frm X} (src : Src P f) (brs : Dec Branch src)
      → (Q : {f : Frm X} → P f → Type ℓ)
      → Dec Q (canopy src brs) → Dec (λ {f} x → Σ[ b ∈ Branch x ] Dec Q (lvs b)) src

    data Pd where

      lf : {f : Frm X} (tgt : P f)
         → Pd (f , η P tgt , tgt) 

      nd : {f : Frm X} {src : Src P f} (tgt : P f)
         → (flr : U (f , src , tgt))
         → (brs : Dec Branch src) 
         → Pd (f , canopy src brs , tgt)

    γ : {f : Frm X} {src : Src P f} {tgt : P f}
       → (pd : Pd (f , src , tgt))
       → (brs : Dec Branch src)
       → Pd (f , canopy src brs , tgt)
    γ (lf tgt) brs = {!!}
    γ (nd {src = src} tgt flr lbrs) brs = {!!}

      where step₁ : Dec (λ x → Σ[ b ∈ Branch x ] Dec Branch (lvs b)) src
            step₁ = canopy-dec src lbrs Branch brs 

    canopy = {!!} 
    canopy-dec = {!!} 


  -- so in this version, there's just a "shadow" μ.  and then we'll need a
  -- shadow ν. how about shadow η?
