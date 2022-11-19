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

module Experimental.NoDecs.TripleOpetopicTypes where

  --
  --  Opetopic Types
  --

  infixl 50 _⊙_

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
    --  Maps of Opetopic Types
    --

    _⇒_ : ∀ {n ℓ} → 𝕆Type n ℓ → 𝕆Type n ℓ → Type ℓ 

    id-map : ∀ {n ℓ} → (X : 𝕆Type n ℓ) → X ⇒ X

    _⊙_ : ∀ {n ℓ} {X Y Z : 𝕆Type n ℓ}
      → Y ⇒ Z → X ⇒ Y → X ⇒ Z

    Frm⇒ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → (σ : X ⇒ Y)
      → Frm X → Frm Y

    --
    --  Laws for maps 
    --
  
    Frm⇒-id : ∀ {n ℓ} (X : 𝕆Type n ℓ) (f : Frm X)
      → Frm⇒ (id-map X) f ↦ f
    {-# REWRITE Frm⇒-id #-}

    Frm⇒-⊙ : ∀ {n ℓ} {X Y Z : 𝕆Type n ℓ}
      → (σ : X ⇒ Y) (τ : Y ⇒ Z) (f : Frm X)
      → Frm⇒ τ (Frm⇒ σ f) ↦ Frm⇒ (τ ⊙ σ) f 
    {-# REWRITE Frm⇒-⊙ #-}

    map-unit-l : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → (σ : X ⇒ Y)
      → id-map Y ⊙ σ ↦ σ
    {-# REWRITE map-unit-l #-}

    map-unit-r : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → (σ : X ⇒ Y)
      → σ ⊙ id-map X ↦ σ
    {-# REWRITE map-unit-r #-}

    map-assoc : ∀ {n ℓ} {X Y Z W : 𝕆Type n ℓ}
      → (ρ : X ⇒ Y) (σ : Y ⇒ Z) (τ : Z ⇒ W)
      → τ ⊙ (σ ⊙ ρ) ↦ τ ⊙ σ ⊙ ρ
    {-# REWRITE map-assoc #-} 

    --
    --  Monadic Structure
    --

    ν : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : Frm Y → Type ℓ}
      → (σ : X ⇒ Y)
      → {f : Frm X} (s : Src P f)
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

    ν-pos : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : Frm Y → Type ℓ}
      → (σ : X ⇒ Y)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → Pos P s → Pos Q (ν σ s ϕ)

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

    ν-lift : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : Frm Y → Type ℓ}
      → (σ : X ⇒ Y)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → Pos Q (ν σ s ϕ) → Pos P s
      
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
    --  Position Computation
    --

    ν-lift-β : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : Frm Y → Type ℓ}
      → (σ : X ⇒ Y)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos P s)
      → ν-lift σ s ϕ (ν-pos {Q = Q} σ s ϕ p) ↦ p
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

    Typ-ν : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : Frm Y → Type ℓ}
      → (σ : X ⇒ Y)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (ν σ s ϕ))
      → Typ Q (ν σ s ϕ) p ↦ Frm⇒ σ (Typ P s (ν-lift σ s ϕ p))
    {-# REWRITE Typ-ν #-}

    ⊚-ν : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : Frm Y → Type ℓ}
      → (σ : X ⇒ Y)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (ν σ s ϕ))
      → ν σ s ϕ ⊚ p ↦ ϕ (ν-lift σ s ϕ p)
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

    ν-ν : ∀ {n ℓ} {X Y Z : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → (R : Frm Z → Type ℓ)
      → (σ : X ⇒ Y) (τ : Y ⇒ Z)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (ψ : (p : Pos Q (ν σ s ϕ)) → R (Frm⇒ τ (Typ Q (ν σ s ϕ) p)))
      → ν {Q = R} τ (ν σ s ϕ) ψ ↦ ν (τ ⊙ σ) s (λ p → ψ (ν-pos σ s ϕ p))
    {-# REWRITE ν-ν #-} 
      
    ν-η : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y)
      → {f : Frm X} (x : P f)
      → (ϕ : (p : Pos P (η P x)) → Q (Frm⇒ σ f))
      → ν σ (η P x) ϕ ↦ η Q (ϕ (η-pos P x))
    {-# REWRITE ν-η #-}

    ν-μ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y)
      → {f : Frm X} (s : Src (Src P) f)
      → (ϕ : (p : Pos P (μ P s)) → Q (Frm⇒ σ (Typ P (μ P s) p)))
      → ν σ (μ P s) ϕ ↦ μ Q (ν σ s (λ p → ν σ (s ⊚ p) (λ q → ϕ (μ-pos P s p q))))
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
      → μ P (ν (id-map X) s (λ p → η P (s ⊚ p))) ↦ s
    {-# REWRITE μ-unit-r #-}

    μ-assoc : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src (Src (Src P)) f)
      → μ P (ν (id-map X) s (λ p → μ P (s ⊚ p))) ↦ μ P (μ (Src P) s)
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
    
    data Pd where

      lf : {f : Frm X} (tgt : P f)
         → Pd (f , η P tgt , tgt) 

      nd : {f : Frm X} (tgt : P f)
         → (brs : Src Branch f)
         → (flr : U (f , ν (id-map X) brs (λ p → stm (brs ⊚ p)) , tgt))
         → Pd (f , μ P (ν (id-map X) brs (λ p → lvs (brs ⊚ p))) , tgt)

    γ : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (ϕ : (p : Pos P src) → Σ[ lvs ∈ Src P (Typ P src p) ] Pd (Typ P src p , lvs , src ⊚ p))
      → Pd (frm , μ P (ν (id-map X) src (λ p → fst (ϕ p))) , tgt)
    γ (lf tgt) ϕ = snd (ϕ (η-pos P tgt))
    γ (nd tgt brs flr) ϕ = nd tgt {!ν (id-map X) brs ψ!} {!!}
      -- let ψ p = [ stm (brs ⊚ p)
      --           , _
      --           , γ (br (brs ⊚ p)) {!!}
      --           ] 
      -- in 

      where ψ : ((p : Pos Branch brs) → Branch (Typ Branch brs p))
            ψ p = [ stm (brs ⊚ p) , {!!} , γ (br (brs ⊚ p)) (λ q → {!ϕ!}) ] 

                -- , γ (br (brs ⊚ p)) (λ q → ϕ (μ-pos (id-map X) Branch P brs (λ r → lvs (brs ⊚ r)) p q))

-- (map-src (id-map X) Branch Branch brs ψ)

-- ν (id-map X) (ν (id-map X) brs ?2)
-- (λ p → lvs (ν (id-map X) brs ?2 ⊚ p))
-- !=
-- μ (Src P)
-- (ν (id-map X) (ν (id-map X) brs (λ p → lvs (brs ⊚ p)))
--  (λ p →
--     ν (id-map X) (ν (id-map X) brs (λ p₁ → lvs (brs ⊚ p₁)) ⊚ p)
--     (λ q →
--        fst (ϕ (μ-pos P (ν (id-map X) brs (λ p₁ → lvs (brs ⊚ p₁))) p q)))))
