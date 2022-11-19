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

module Experimental.NoDecs.NoPosOpType4 where

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

    ν₂ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {R : {f : Frm X} → P f → Type ℓ}
      → (ψ : {f : Frm X} (p : P f) (r : R p) → Q f)
      → {f : Frm X} (s : Src P f) (δ : Dec R s)
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

    ν₂-dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {R : {f : Frm X} → P f → Type ℓ}
      → {T : {f : Frm X} → Q f → Type ℓ}
      → (ψ : {f : Frm X} (p : P f) (r : R p) → Q f)
      → {f : Frm X} (s : Src P f) (δ : Dec R s)
      → Dec T (ν₂ ψ s δ) → Dec (λ p → Σ[ r ∈ R p ] T (ψ p r)) s 

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

    ν-ν₂ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q T : Frm X → Type ℓ}
      → {R : {f : Frm X} → P f → Type ℓ}
      → (ψ : {f : Frm X} (p : P f) (r : R p) → Q f)
      → (σ : {f : Frm X} → Q f → T f)
      → {f : Frm X} (s : Src P f) (δ : Dec R s)
      → ν σ (ν₂ ψ s δ) ↦ ν₂ (λ p r → σ (ψ p r)) s δ
    {-# REWRITE ν-ν₂ #-}

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
    --  Two argument naturality 
    -- 

    ν₂-ν : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {O P Q : Frm X → Type ℓ}
      → {R : {f : Frm X} → P f → Type ℓ}
      → (σ : {f : Frm X} → O f → P f)
      → {f : Frm X} (s : Src O f) (δ : Dec R (ν σ s))
      → (ψ : {f : Frm X} (p : P f) (r : R p) → Q f)
      → ν₂ ψ (ν σ s) δ ↦ ν₂ (λ o r → ψ (σ o) r) s (ν-dec σ s δ) 
    {-# REWRITE ν₂-ν #-}

    ν₂-ν₂ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q U : Frm X → Type ℓ}
      → {R : {f : Frm X} → P f → Type ℓ}
      → {T : {f : Frm X} → Q f → Type ℓ}
      → (ψ : {f : Frm X} (p : P f) (r : R p) → Q f)
      → (ϕ : {f : Frm X} (q : Q f) (t : T q) → U f) 
      → {f : Frm X} (s : Src P f) (δ : Dec R s) (ε : Dec T (ν₂ ψ s δ))
      → ν₂ ϕ (ν₂ ψ s δ) ε ↦ ν₂ (λ p rt → ϕ (ψ p (fst rt)) (snd rt)) s (ν₂-dec ψ s δ ε)
    {-# REWRITE ν₂-ν₂ #-}

    ν₂-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P Q : Frm X → Type ℓ)
      → (R : {f : Frm X} → P f → Type ℓ)
      → {f : Frm X} (x : P f) (δ : Dec R (η P x))
      → (ψ : {f : Frm X} (p : P f) (r : R p) → Q f)
      → ν₂ ψ (η P x) δ ↦ η Q (ψ x (η-dec x δ)) 
    {-# REWRITE ν₂-η #-}

    ν₂-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P Q : Frm X → Type ℓ)
      → (R : {f : Frm X} → P f → Type ℓ)
      → {f : Frm X} (s : Src (Src P) f) (δ : Dec R (μ P s))
      → (ψ : {f : Frm X} (p : P f) (r : R p) → Q f)
      → ν₂ ψ (μ P s) δ ↦ μ Q (ν₂ (ν₂ ψ) s (μ-dec s δ))
    {-# REWRITE ν₂-μ #-}

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
    
    data Pd where

      lf : {f : Frm X} (tgt : P f)
         → Pd (f , η P tgt , tgt) 

      nd : {f : Frm X} (src : Src P f) (tgt : P f)
         → (flr : U (f , src , tgt))
         → (lvs : Dec (λ {f} _ → Src P f) src)
         → (brs : Dec Branch src) 
         → Pd (f , μ P {!lvs!} , tgt)

    -- γ : {frm : Frm X} {src : Src P frm} {tgt : P frm}
    --   → (pd : Pd (frm , src , tgt ))
    --   → (brs : Dec Branch src)
    --   → Pd (frm , μ P (ν₂ (λ p → lvs) src brs) , tgt)
    -- γ (lf tgt) brs = br (η-dec tgt brs)
    -- γ (nd src tgt flr lbrs) brs = {!lbrs!}

    --   where lbrs' : Dec (Dec Branch) (ν₂ (λ p → lvs) src lbrs)
    --         lbrs' = μ-dec (ν₂ (λ p → lvs) src lbrs) brs

    --         lbrs'' : Dec (λ p → Σ-syntax (Branch p) (λ r → Dec Branch (lvs r))) src
    --         lbrs'' = ν₂-dec (λ p → lvs) src lbrs lbrs' 

    --         lbrs''' : Dec Branch src
    --         lbrs''' = {!!} 

