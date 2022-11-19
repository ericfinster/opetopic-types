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

module Experimental.NoDecs.NoPosOpType2 where

  --
  --  Opetopic Types
  --

  𝕆Type : ℕ → (ℓ : Level) → Type (ℓ-suc ℓ)
  Frm : ∀ {n ℓ} → 𝕆Type n ℓ → Type ℓ

  Src : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → Frm X → Type ℓ

  postulate

    Dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : {f : Frm X} → P f → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → Type ℓ 

    split : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → (R : {f : Frm X} → Q f → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : {f : Frm X} (p : P f) → Q f)
      → (ψ : {f : Frm X} (p : P f) → R (ϕ p))
      → Σ[ t ∈ Src Q f ] Dec R t

    unsplit : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → (R : {f : Frm X} → P f → Type ℓ)
      → {f : Frm X} (s : Src P f) (δ : Dec R s)
      → (ϕ : {f : Frm X} (p : P f) → R p → Q f)
      → Src Q f 

    -- 
    --  Monadic Structure
    --

    η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (x : P f)
      → Src P f 

    μ : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : {f : Frm X} → P f → Src Q f)
      → Src Q f 

    --
    --  Decomposing Decorations
    --

    -- INCOMPLETE : there should be compatibility conditions with the
    -- monad and naturality laws.

    η-dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : {f : Frm X} → P f → Type ℓ}
      → {f : Frm X} (x : P f)
      → Dec Q (η P x) → Q x

    μ-dec : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {R : {f : Frm X} → Q f → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : {f : Frm X} → P f → Src Q f)
      → Dec R (μ s ϕ) → Dec (λ p → Dec R (ϕ p)) s 

    --
    --  Monad Laws
    --

    μ-unit-l : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P Q : Frm X → Type ℓ)
      → (f : Frm X) (x : P f)
      → (ϕ : {f : Frm X} → P f → Src Q f)
      → μ (η P x) ϕ ↦ ϕ x
    {-# REWRITE μ-unit-l #-}

    μ-unit-r : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ s (η P) ↦ s
    {-# REWRITE μ-unit-r #-}

    μ-assoc : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P Q R : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → (ϕ : {f : Frm X} → P f → Src Q f)
      → (ψ : {f : Frm X} → Q f → Src R f)
      → μ (μ s ϕ) ψ ↦ μ s (λ p → μ (ϕ p) ψ)
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
         → (brs : Dec Branch src) 
         → Pd (f , μ (unsplit _ src brs (λ _ → lvs)) (λ x → x) , tgt)

    γ : {f : Frm X} {src : Src P f} {tgt : P f}
       → (pd : Pd (f , src , tgt))
       → (brs : Dec Branch src) 
       → Pd (f , μ (unsplit _ src brs (λ _ → lvs)) (λ x → x) , tgt)
    γ (lf tgt) brs = {!br (η-dec tgt brs)!}
    γ (nd src tgt flr lbrs) brs = {!!}

  --   γ (lf tgt) brs = snd (η-dec tgt brs)
  --   γ (nd tgt lbrs flr) brs = nd tgt lbrs'' {!flr!}

  --     where brs' : Dec (λ p → Dec (λ {f} t → Σ-syntax (Src P f) (λ s → Pd (f , s , t))) (lvs p)) lbrs
  --           brs' = μ-dec lbrs lvs brs 

  --           lbrs' : Src (λ f → Σ (Branch f) (λ p →  Dec (λ {f = f₁} t → Σ-syntax (Src P f₁) (λ s → Pd (f₁ , s , t))) (lvs p))) _
  --           lbrs' = zip lbrs brs' 

  --           lbrs'' : Src Branch _
  --           lbrs'' = μ lbrs' (λ { {f} (b , δ) →
  --             η Branch [ stm b , μ (zip (lvs b) δ) (λ tsp → tsp .snd .fst) , γ (br b) δ ] })

  Src {zero} P f = P tt*
  Src {suc n} P f = Pd P f

  -- μ {zero} s ϕ = ϕ s
  -- μ {suc n} (lf tgt) ϕ = lf tgt 
  -- μ {suc n} {X = X} {Q = Q} (nd {f} tgt brs flr) ϕ = {!ϕ (flr)!}

  --   -- where w : Pd Q (f , μ brs (λ br₁ → η (snd X) (stm br₁)) , tgt)
  --   --       w = ϕ flr 
