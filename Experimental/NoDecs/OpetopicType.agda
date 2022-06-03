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

module Experimental.NoDecs.OpetopicType where

  --
  --  Opetopic Types
  --
  
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
    → {P : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (p : Pos P s) → Frm X 

  {-# TERMINATING #-}
  _⊚_ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (p : Pos P s)
    → P (Typ s p)

  --
  --  Maps of Opetopic Types
  --

  infixl 50 _⊙_
  
  postulate
  
    _⇒_ : ∀ {n ℓ} → 𝕆Type n ℓ → 𝕆Type n ℓ → Type ℓ 

    Frm⇒ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → (σ : X ⇒ Y)
      → Frm X → Frm Y

    Src⇒ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {Q : Frm Y → Type ℓ}
      → (σₙ : X ⇒ Y) (σₛₙ : {f : Frm X} → P f → Q (Frm⇒ σₙ f))
      → {f : Frm X}
      → Src P f → Src Q (Frm⇒ σₙ f) 

    id-map : ∀ {n ℓ} → (X : 𝕆Type n ℓ) → X ⇒ X

    _⊙_ : ∀ {n ℓ} {X Y Z : 𝕆Type n ℓ}
      → Y ⇒ Z → X ⇒ Y → X ⇒ Z

  --
  --  Equations for maps 
  --
  
  postulate
  
    Frm⇒-id : ∀ {n ℓ} (X : 𝕆Type n ℓ) (f : Frm X)
      → Frm⇒ (id-map X) f ↦ f
    {-# REWRITE Frm⇒-id #-}

    Frm⇒-⊙ : ∀ {n ℓ} {X Y Z : 𝕆Type n ℓ}
      → (σ : X ⇒ Y) (τ : Y ⇒ Z) (f : Frm X)
      → Frm⇒ (τ ⊙ σ) f ↦ Frm⇒ τ (Frm⇒ σ f)
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

  η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (x : P f)
    → Src P f 

  postulate

    η-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → {f : Frm X} (x : P f)
      → Pos P (η P x)

    μ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ s p)))
      → Src Q (Frm⇒ σ f)

    μ-pos : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ s p)))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → Pos Q (μ Q σ s ϕ) 

    μ-fst : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ s p)))
      → (p : Pos Q (μ Q σ s ϕ))
      → Pos P s  

    μ-snd : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ s p)))
      → (p : Pos Q (μ Q σ s ϕ))
      → Pos Q (ϕ (μ-fst Q σ s ϕ p))

  --
  --  Monadic Laws
  --

  postulate

    -- Typing and Inhabitants of μ and η
    Typ-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (p : Pos P (η P x))
      → Typ (η P x) p ↦ f
    {-# REWRITE Typ-η #-}

    ⊚-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (p : Pos P (η P x))
      → η P x ⊚ p ↦ x
    {-# REWRITE ⊚-η #-}

    Typ-μ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ s p)))
      → (p : Pos Q (μ Q σ s ϕ))
      → Typ (μ Q σ s ϕ) p ↦ Typ (ϕ (μ-fst Q σ s ϕ p)) (μ-snd Q σ s ϕ p)
    {-# REWRITE Typ-μ #-}

    ⊚-μ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ s p)))
      → (p : Pos Q (μ Q σ s ϕ))
      → μ Q σ s ϕ ⊚ p ↦ ϕ (μ-fst Q σ s ϕ p) ⊚ μ-snd Q σ s ϕ p
    {-# REWRITE ⊚-μ #-}

    -- Laws for positions
    -- η-pos-elim-β : ∀ {n ℓ ℓ'} {X : 𝕆Type n ℓ}
    --   → {P : Frm X → Type ℓ}
    --   → {f : Frm X} (x : P f)
    --   → (Q : Pos P (η P x) → Type ℓ')
    --   → (q : Q (η-pos P x))
    --   → η-pos-elim x Q q (η-pos P x) ↦ q
    -- {-# REWRITE η-pos-elim-β #-}

    μ-fst-β : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ s p)))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → μ-fst Q σ s ϕ (μ-pos Q σ s ϕ p q) ↦ p 
    {-# REWRITE μ-fst-β #-}

    μ-snd-β : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ s p)))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → μ-snd Q σ s ϕ (μ-pos Q σ s ϕ p q) ↦ q
    {-# REWRITE μ-snd-β #-}

    μ-pos-η : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ s p)))
      → (p : Pos Q (μ Q σ s ϕ))
      → μ-pos Q σ s ϕ (μ-fst Q σ s ϕ p) (μ-snd Q σ s ϕ p) ↦ p
    {-# REWRITE μ-pos-η #-}
    
    -- Monad Laws
    unit-left : ∀ {n ℓ} (X Y : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y)
      → (f : Frm X) (x : P f)
      → (ϕ : (p : Pos P (η P x)) → Src Q (Frm⇒ σ f))
      → μ Q σ (η P x) ϕ ↦ ϕ (η-pos P x)
    {-# REWRITE unit-left #-}
    
    unit-right : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ P (id-map X) s (λ p → η P (s ⊚ p)) ↦ s
    {-# REWRITE unit-right #-}
    
    μ-assoc : ∀ {n ℓ} (X Y Z : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → (R : Frm Z → Type ℓ)
      → (σ : X ⇒ Y) (τ : Y ⇒ Z) 
      → (f : Frm X) (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ s p)))
      → (ψ : (pq : Pos Q (μ Q σ s ϕ)) → Src R (Frm⇒ τ (Typ (μ Q σ s ϕ) pq)))
      → μ R τ (μ Q σ s ϕ) ψ ↦ μ R (τ ⊙ σ) s (λ p → μ R τ (ϕ p) (λ q → ψ (μ-pos Q σ s ϕ p q)))
    {-# REWRITE μ-assoc #-}

    -- Interaction with maps
    Src⇒-η : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ) 
      → (σₙ : X ⇒ Y) (σₛₙ : {f : Frm X} → P f → Q (Frm⇒ σₙ f))
      → {f : Frm X} (p : P f)
      → Src⇒ {Q = Q} σₙ σₛₙ (η P p) ↦ η Q (σₛₙ p) 

    Src⇒-μ : ∀ {n ℓ} {X Y Z : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (R : Frm Z → Type ℓ)
      → (σₙ : X ⇒ Y) 
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σₙ (Typ s p)))
      → (τₙ : Y ⇒ Z) (τₛₙ : {f : Frm Y} → Q f → R (Frm⇒ τₙ f))
      → Src⇒ {Q = R} τₙ τₛₙ (μ Q σₙ s ϕ) ↦ μ R (τₙ ⊙ σₙ) s (λ p → Src⇒ {Q = R} τₙ τₛₙ (ϕ p))

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
         → Pd (f , tgt , η P tgt) 

      nd : {f : Frm X} (tgt : P f)
         → (brs : Src Branch f)
         → (flr : U (f , tgt , μ P (id-map X) brs (λ p → η P (stm (brs ⊚ p)))))
         → Pd (f , tgt , μ P (id-map X) brs (λ p → lvs (brs ⊚ p)))

  Src {zero} P _ = P tt*
  Src {suc n} U = Pd U

  Pos {zero} P s = Lift Unit
  Pos {suc n} U (lf tgt) = Lift ⊥
  Pos {suc n} U (nd tgt brs flr) =
    Unit ⊎ (Σ[ p ∈ Pos (Branch U) brs ]
            Pos U (br (brs ⊚ p)))

  Typ {zero} s p = tt*
  Typ {suc n} {X = X , P} {P = U} (nd tgt brs flr) (inl _) =
    _ , tgt , μ P (id-map X) brs (λ p → η P (stm (brs ⊚ p)))
  Typ {suc n} (nd tgt brs flr) (inr (p , q)) = Typ (br (brs ⊚ p)) q

  _⊚_ {zero} s p = s
  _⊚_ {suc n} (nd tgt brs flr) (inl _) = flr
  _⊚_ {suc n} (nd tgt brs flr) (inr (p , q)) = br (brs ⊚ p) ⊚ q

  η = {!!} 
  -- η {zero} P x = x
  -- η {suc n} {X = X , P} U {f = f , t , s} x = 
  --   let brs = μ (Branch U) (id-map X) s (λ p → η (Branch U)
  --         [ s ⊚ p , η P (s ⊚ p) , lf (s ⊚ p) ])
  --   in nd t brs x
