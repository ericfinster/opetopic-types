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

  {-# TERMINATING #-}
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

  infixl 50 _⊙_
  
  postulate
  
    _⇒_ : ∀ {n ℓ} → 𝕆Type n ℓ → 𝕆Type n ℓ → Type ℓ 

    id-map : ∀ {n ℓ} → (X : 𝕆Type n ℓ) → X ⇒ X

    _⊙_ : ∀ {n ℓ} {X Y Z : 𝕆Type n ℓ}
      → Y ⇒ Z → X ⇒ Y → X ⇒ Z

    Frm⇒ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → (σ : X ⇒ Y)
      → Frm X → Frm Y

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

    μ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → Src Q (Frm⇒ σ f)

    μ-pos : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → Pos Q (μ σ P Q s ϕ) 

    μ-fst : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (μ σ P Q s ϕ))
      → Pos P s  

    μ-snd : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (μ σ P Q s ϕ))
      → Pos Q (ϕ (μ-fst σ P Q s ϕ p))


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
  --  Monadic Laws
  --

  postulate

    -- Typing and Inhabitants of μ and η
    Typ-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (p : Pos P (η P x))
      → Typ P (η P x) p ↦ f
    {-# REWRITE Typ-η #-}

    Typ-μ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (μ σ P Q s ϕ))
      → Typ Q (μ σ P Q s ϕ) p ↦ Typ Q (ϕ (μ-fst σ P Q s ϕ p)) (μ-snd σ P Q s ϕ p)
    {-# REWRITE Typ-μ #-}

    -- BUG! Why do we need this ?!?
    
    -- Oh!!! I have an idea!  It's because id-map eliminates the
    -- occurence of Frm⇒ in the type of the decoration.  Hence it no
    -- longer matches!

    Typ-μ-idmap : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → (P Q : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ P s p))
      → (p : Pos Q (μ (id-map X) P Q s ϕ))
      → Typ Q (μ (id-map X) P Q s ϕ) p ↦ Typ Q (ϕ (μ-fst (id-map X) P Q s ϕ p)) (μ-snd (id-map X) P Q s ϕ p)
    {-# REWRITE Typ-μ-idmap #-}

    ⊚-η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (p : Pos P (η P x))
      → η P x ⊚ p ↦ x
    {-# REWRITE ⊚-η #-}

    ⊚-μ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (μ σ P Q s ϕ))
      → μ σ P Q s ϕ ⊚ p ↦ ϕ (μ-fst σ P Q s ϕ p) ⊚ μ-snd σ P Q s ϕ p
    {-# REWRITE ⊚-μ #-}

    -- BUG!  Same as above.
    ⊚-μ-idmap : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → (P Q : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ P s p))
      → (p : Pos Q (μ (id-map X) P Q s ϕ))
      → μ (id-map X) P Q s ϕ ⊚ p ↦ (ϕ (μ-fst (id-map X) P Q s ϕ p) ⊚ μ-snd (id-map X) P Q s ϕ p) 
    {-# REWRITE ⊚-μ-idmap #-}

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
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → μ-fst σ P Q s ϕ (μ-pos σ P Q s ϕ p q) ↦ p 
    {-# REWRITE μ-fst-β #-}

    μ-snd-β : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → μ-snd σ P Q s ϕ (μ-pos σ P Q s ϕ p q) ↦ q
    {-# REWRITE μ-snd-β #-}

    μ-pos-η : ∀ {n ℓ} {X Y : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y) {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (μ σ P Q s ϕ))
      → μ-pos σ P Q s ϕ (μ-fst σ P Q s ϕ p) (μ-snd σ P Q s ϕ p) ↦ p
    {-# REWRITE μ-pos-η #-}
    
    -- Monad Laws
    unit-left : ∀ {n ℓ} (X Y : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → (σ : X ⇒ Y)
      → (f : Frm X) (x : P f)
      → (ϕ : (p : Pos P (η P x)) → Src Q (Frm⇒ σ f))
      → μ σ P Q (η P x) ϕ ↦ ϕ (η-pos P x)
    {-# REWRITE unit-left #-}

    unit-right : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ (id-map X) P P s (λ p → η P (s ⊚ p)) ↦ s
    {-# REWRITE unit-right #-}

    μ-assoc : ∀ {n ℓ} (X Y Z : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → (R : Frm Z → Type ℓ)
      → (σ : X ⇒ Y) (τ : Y ⇒ Z) 
      → (f : Frm X) (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
      → (ψ : (pq : Pos Q (μ σ P Q s ϕ)) → Src R (Frm⇒ τ (Typ Q (μ σ P Q s ϕ) pq)))
      → μ τ Q R (μ σ P Q s ϕ) ψ ↦ μ (τ ⊙ σ) P R s (λ p → μ τ Q R (ϕ p) (λ q → ψ (μ-pos σ P Q s ϕ p q)))
    {-# REWRITE μ-assoc #-}

    μ-assoc-idmap-l : ∀ {n ℓ} (X Z : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (Q : Frm X → Type ℓ)
      → (R : Frm Z → Type ℓ)
      → (τ : X ⇒ Z) 
      → (f : Frm X) (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ P s p))
      → (ψ : (pq : Pos Q (μ (id-map X) P Q s ϕ)) → Src R (Frm⇒ τ (Typ Q (μ (id-map X) P Q s ϕ) pq)))
      → μ τ Q R (μ (id-map X) P Q s ϕ) ψ ↦ μ τ P R s (λ p → μ τ Q R (ϕ p) (λ q → ψ (μ-pos (id-map X) P Q s ϕ p q)))
    {-# REWRITE μ-assoc-idmap-l #-}

  smap : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → (Q : Frm X → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Typ P s p))
    → Src Q f
  smap {X = X} P Q s ϕ = μ (id-map X) P Q s (λ p → η Q (ϕ p))

  smap-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → (Q : Frm X → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Typ P s p))
    → (p : Pos P s) → Pos Q (smap P Q s ϕ)
  smap-pos {X = X} P Q s ϕ p = μ-pos (id-map X) P Q s (λ p → η Q (ϕ p)) p (η-pos Q (ϕ p)) 

  smap-pos-inv : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → (Q : Frm X → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Typ P s p))
    → Pos Q (smap P Q s ϕ) → Pos P s
  smap-pos-inv {X = X} P Q s ϕ p = μ-fst (id-map X) P Q s (λ p → η Q (ϕ p)) p 

  𝕆Type zero ℓ = Lift Unit
  𝕆Type (suc n) ℓ =
    Σ[ X ∈ 𝕆Type n ℓ ]
    ((f : Frm X) → Type ℓ)

  Frm {zero} X = Lift Unit
  Frm {suc n} (X , P) = 
    Σ[ f ∈ Frm X ]
    Σ[ src ∈ Src P f ] 
    P f

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
        br : Pd (f , lvs , stm)

    open Branch public
    
    data Pd where

      lf : {f : Frm X} (tgt : P f)
         → Pd (f , η P tgt , tgt) 

      nd : {f : Frm X} (tgt : P f)
         → (brs : Src Branch f)
         → (flr : U (f , μ (id-map X) Branch P brs (λ p → η P (stm (brs ⊚ p))) , tgt))
         → Pd (f , μ (id-map X) Branch P brs (λ p → lvs (brs ⊚ p)) , tgt)

  Src {zero} P _ = P tt*
  Src {suc n} U = Pd U

  Pos {zero} P s = Lift Unit
  Pos {suc n} U (lf tgt) = Lift ⊥
  Pos {suc n} U (nd tgt brs flr) =
    Unit ⊎ (Σ[ p ∈ Pos (Branch U) brs ]
            Pos U (br (brs ⊚ p)))

  Typ {zero} P s p = tt*
  Typ {suc n} {X = X , P} U (nd {f = f} tgt brs flr) (inl _) =
    f , μ (id-map X) (Branch U) P brs (λ p → η P (stm (brs ⊚ p))) , tgt 
  Typ {suc n} U (nd tgt brs flr) (inr (p , q)) = Typ U (br (brs ⊚ p)) q

  _⊚_ {zero} s p = s
  _⊚_ {suc n} (nd tgt brs flr) (inl _) = flr
  _⊚_ {suc n} (nd tgt brs flr) (inr (p , q)) = br (brs ⊚ p) ⊚ q

  η {zero} P x = x
  η {suc n} {X = X , P} U {f = f , s , t} x =
    let brs = μ (id-map X) P (Branch U) s (λ p → η (Branch U) [ s ⊚ p , η P (s ⊚ p) , lf (s ⊚ p) ])
    in nd t brs x
      

