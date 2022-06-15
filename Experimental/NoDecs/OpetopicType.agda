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

  η-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (x : P f)
    → Pos P (η P x)

  η-pos-elim : ∀ {n ℓ ℓ'} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → {f : Frm X} (x : P f)
    → (Q : Pos P (η P x) → Type ℓ')
    → (q : Q (η-pos P x))
    → (p : Pos P (η P x)) → Q p

  μ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
    → (P : Frm X → Type ℓ)
    → (Q : Frm Y → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Src Q (Frm⇒ σ (Typ P s p)))
    → Src Q (Frm⇒ σ f)
    
  postulate

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
  --  Equational Structure
  --
  
  postulate

    --
    --  Laws for maps
    -- 
  
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
    --  Laws for positions types and inhabitants
    --
    
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

    --
    -- Laws for positions
    --
    
    η-pos-elim-β : ∀ {n ℓ ℓ'} {X : 𝕆Type n ℓ}
      → {P : Frm X → Type ℓ}
      → {f : Frm X} (x : P f)
      → (Q : Pos P (η P x) → Type ℓ')
      → (q : Q (η-pos P x))
      → η-pos-elim x Q q (η-pos P x) ↦ q
    {-# REWRITE η-pos-elim-β #-}

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

    -- Extra law needed due to lack of η-expansion for positions
    map-η : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
      → (P : Frm X → Type ℓ)
      → (Q : Frm Y → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (μ σ P Q s (λ p → η Q (ϕ p))))
      → μ-pos σ P Q s (λ p → η Q (ϕ p)) (μ-fst σ P Q s (λ p → η Q (ϕ p)) p)
         (η-pos Q (ϕ (μ-fst σ P Q s (λ p → η Q (ϕ p)) p))) ↦ p
    {-# REWRITE map-η #-}

    -- BUG! id-map version of above
    map-η-idmap : ∀ {n ℓ} {X : 𝕆Type n ℓ} 
      → (P : Frm X → Type ℓ)
      → (Q : Frm X → Type ℓ)
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (p : Pos Q (μ (id-map X) P Q s (λ p → η Q (ϕ p))))
      → μ-pos (id-map X) P Q s (λ p → η Q (ϕ p)) (μ-fst (id-map X) P Q s (λ p → η Q (ϕ p)) p)
         (η-pos Q (ϕ (μ-fst (id-map X) P Q s (λ p → η Q (ϕ p)) p))) ↦ p
    {-# REWRITE map-η-idmap #-}

    --
    -- Monad Laws
    --
    
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

    -- BUG!  Specialized for id-map ...
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

  map-src : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
    → (P : Frm X → Type ℓ)
    → (Q : Frm Y → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
    → Src Q (Frm⇒ σ f)
  map-src σ P Q s ϕ = μ σ P Q s (λ p → η Q (ϕ p))

  map-src-lift : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
    → (P : Frm X → Type ℓ)
    → (Q : Frm Y → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
    → (p : Pos Q (map-src σ P Q s ϕ))
    → Pos P s
  map-src-lift σ P Q s ϕ = μ-fst σ P Q s (λ p → η Q (ϕ p))  

  map-src-pos : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
    → (P : Frm X → Type ℓ)
    → (Q : Frm Y → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
    → (p : Pos P s)
    → Pos Q (map-src σ P Q s ϕ)
  map-src-pos σ P Q s ϕ p = μ-pos σ P Q s (λ p → η Q (ϕ p)) p (η-pos Q (ϕ p))

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
         → (flr : U (f , μ (id-map X) Branch P brs (λ p → η P (stm (brs ⊚ p))) , tgt))
         → Pd (f , μ (id-map X) Branch P brs (λ p → lvs (brs ⊚ p)) , tgt)


    data PdPos : {f : Frm (X , P)} → Pd f → Type ℓ where

      nd-here : {f : Frm X} {tgt : P f}
         → {brs : Src Branch f}
         → {flr : U (f , μ (id-map X) Branch P brs (λ p → η P (stm (brs ⊚ p))) , tgt)}
         → PdPos (nd tgt brs flr)

      nd-there : {f : Frm X} {tgt : P f}
         → {brs : Src Branch f}
         → {flr : U (f , μ (id-map X) Branch P brs (λ p → η P (stm (brs ⊚ p))) , tgt)}
         → (p : Pos Branch brs) (q : PdPos (br (brs ⊚ p)))
         → PdPos (nd tgt brs flr)

    γ : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (ϕ : (p : Pos P src) → Σ[ lvs ∈ Src P (Typ P src p) ] Pd (Typ P src p , lvs , src ⊚ p))
      → Pd (frm , μ (id-map X) P P src (λ p → fst (ϕ p)) , tgt)
    γ (lf tgt) ϕ = snd (ϕ (η-pos P tgt))
    γ (nd tgt brs flr) ϕ = 
      let ψ p = [ stm (brs ⊚ p)
                , μ (id-map X) P P (lvs (brs ⊚ p)) (λ q → fst (ϕ (μ-pos (id-map X) Branch P brs (λ r → lvs (brs ⊚ r)) p q)))
                , γ (br (brs ⊚ p)) (λ q → ϕ (μ-pos (id-map X) Branch P brs (λ r → lvs (brs ⊚ r)) p q))
                ] 
      in nd tgt (map-src (id-map X) Branch Branch brs ψ) flr

    γ-inl : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (ϕ : (p : Pos P src) → Σ[ lvs ∈ Src P (Typ P src p) ] Pd (Typ P src p , lvs , src ⊚ p))
      → (p : PdPos pd) → PdPos (γ pd ϕ)
    γ-inl (nd tgt brs flr) ϕ nd-here = nd-here
    γ-inl (nd tgt brs flr) ϕ (nd-there p q) = 
      let ψ p = [ stm (brs ⊚ p)
                , μ (id-map X) P P (lvs (brs ⊚ p)) (λ q → fst (ϕ (μ-pos (id-map X) Branch P brs (λ r → lvs (brs ⊚ r)) p q)))
                , γ (br (brs ⊚ p)) (λ q → ϕ (μ-pos (id-map X) Branch P brs (λ r → lvs (brs ⊚ r)) p q))
                ] 
          p' = map-src-pos (id-map X) Branch Branch brs ψ p 
      in nd-there p' (γ-inl (br (brs ⊚ p)) (λ q → ϕ (μ-pos (id-map X) Branch P brs (λ r → lvs (brs ⊚ r)) p q)) q )

    γ-inr : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (ϕ : (p : Pos P src) → Σ[ lvs ∈ Src P (Typ P src p) ] Pd (Typ P src p , lvs , src ⊚ p))
      → (p : Pos P src) (q : PdPos (snd (ϕ p)))
      → PdPos (γ pd ϕ)
    γ-inr (lf tgt) ϕ p q = 
      η-pos-elim tgt (λ p → PdPos (snd (ϕ p)) → PdPos (snd (ϕ (η-pos P tgt)))) (λ x → x) p q
    γ-inr (nd tgt brs flr) ϕ pq r = 
      let p = μ-fst (id-map X) Branch P brs (λ p' → lvs (brs ⊚ p')) pq
          q = μ-snd (id-map X) Branch P brs (λ p' → lvs (brs ⊚ p')) pq
          ψ p = [ stm (brs ⊚ p)
                , μ (id-map X) P P (lvs (brs ⊚ p)) (λ q → fst (ϕ (μ-pos (id-map X) Branch P brs (λ r → lvs (brs ⊚ r)) p q)))
                , γ (br (brs ⊚ p)) (λ q → ϕ (μ-pos (id-map X) Branch P brs (λ r → lvs (brs ⊚ r)) p q))
                ] 
          p' = map-src-pos (id-map X) Branch Branch brs ψ p 
      in nd-there p' (γ-inr (br (brs ⊚ p)) (λ q → ϕ (μ-pos (id-map X) Branch P brs (λ r → lvs (brs ⊚ r)) p q)) q r) 

    γ-pos-elim : {frm : Frm X} {src : Src P frm} {tgt : P frm}
      → (pd : Pd (frm , src , tgt ))
      → (ϕ : (p : Pos P src) → Σ[ lvs ∈ Src P (Typ P src p) ] Pd (Typ P src p , lvs , src ⊚ p))
      → ∀ {ℓ'} (B : PdPos (γ pd ϕ) → Type ℓ')
      → (inl* : (p : PdPos pd) → B (γ-inl pd ϕ p))
      → (inr* : (p : Pos P src) (q : PdPos (snd (ϕ p))) → B (γ-inr pd ϕ p q))
      → (p : PdPos (γ pd ϕ)) → B p
    γ-pos-elim (lf tgt) ϕ B inl* inr* p = inr* (η-pos P tgt) p
    γ-pos-elim (nd tgt brs flr) ϕ B inl* inr* nd-here = inl* nd-here
    γ-pos-elim (nd tgt brs flr) ϕ B inl* inr* (nd-there u v) = 
      let ψ p = [ stm (brs ⊚ p)
                , μ (id-map X) P P (lvs (brs ⊚ p)) (λ q → fst (ϕ (μ-pos (id-map X) Branch P brs (λ r → lvs (brs ⊚ r)) p q)))
                , γ (br (brs ⊚ p)) (λ q → ϕ (μ-pos (id-map X) Branch P brs (λ r → lvs (brs ⊚ r)) p q))
                ] 
          u' = map-src-lift (id-map X) Branch Branch brs ψ u
      in γ-pos-elim (br (brs ⊚ u')) (λ q → ϕ (μ-pos (id-map X) Branch P brs (λ r → lvs (brs ⊚ r)) u' q))
           (λ v' → B (nd-there u v')) (λ q → inl* (nd-there u' q))
           (λ q → inr* (μ-pos (id-map X) Branch P brs (λ r → lvs (brs ⊚ r)) u' q)) v

    postulate

      γ-pos-elim-inl-β : {frm : Frm X} {src : Src P frm} {tgt : P frm}
        → (pd : Pd (frm , src , tgt ))
        → (ϕ : (p : Pos P src) → Σ[ lvs ∈ Src P (Typ P src p) ] Pd (Typ P src p , lvs , src ⊚ p))
        → ∀ {ℓ'} (B : PdPos (γ pd ϕ) → Type ℓ')
        → (inl* : (p : PdPos pd) → B (γ-inl pd ϕ p))
        → (inr* : (p : Pos P src) (q : PdPos (snd (ϕ p))) → B (γ-inr pd ϕ p q))
        → (p : PdPos pd)
        → γ-pos-elim pd ϕ B inl* inr* (γ-inl pd ϕ p) ↦ inl* p
      {-# REWRITE γ-pos-elim-inl-β #-}
        
      γ-pos-elim-inr-β : {frm : Frm X} {src : Src P frm} {tgt : P frm}
        → (pd : Pd (frm , src , tgt ))
        → (ϕ : (p : Pos P src) → Σ[ lvs ∈ Src P (Typ P src p) ] Pd (Typ P src p , lvs , src ⊚ p))
        → ∀ {ℓ'} (B : PdPos (γ pd ϕ) → Type ℓ')
        → (inl* : (p : PdPos pd) → B (γ-inl pd ϕ p))
        → (inr* : (p : Pos P src) (q : PdPos (snd (ϕ p))) → B (γ-inr pd ϕ p q))
        → (p : Pos P src) (q : PdPos (snd (ϕ p)))
        → γ-pos-elim pd ϕ B inl* inr* (γ-inr pd ϕ p q) ↦ inr* p q
      {-# REWRITE γ-pos-elim-inr-β #-}
      

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
    Frm⇒ σₙ frm , map-src σₙ P Q src (λ p → σₛₙ (src ⊚ p)) , σₛₙ tgt

  η {zero} P x = x
  η {suc n} {X = X , P} U {f = frm , src , tgt} x =
    let brs = map-src (id-map X) P (Branch U) src (λ p → [ src ⊚ p , η P (src ⊚ p) , lf (src ⊚ p) ])
    in nd tgt brs x

  η-pos {zero} P x = tt*
  η-pos {suc n} P x = inl tt

  η-pos-elim {zero} x Q q p = q
  η-pos-elim {suc n} x Q q (inl u) = q

  μ {zero} {X = X} σ P Q s ϕ = ϕ tt*
  μ {suc n} {X = X , P} (σₙ , σₛₙ) U V (lf tgt) ϕ = lf (σₛₙ tgt)
  μ {suc n} {X = X , P} {Y , Q} (σₙ , σₛₙ) U V (nd {f} tgt brs flr) ϕ = γ V w ϕ'

    where src' : Src Q (Frm⇒ σₙ f)
          src' = map-src σₙ (Branch U) Q brs (λ p → σₛₙ (stm (brs ⊚ p)))

          w : Pd V (Frm⇒ σₙ f , src' , σₛₙ tgt)
          w = ϕ (inl tt)

          ϕ' : (p : Pos Q src') → Σ[ lvs ∈ Src Q (Typ Q src' p) ] (Pd V (Typ Q src' p , lvs , src' ⊚ p))
          ϕ' p = map-src σₙ P Q (lvs (brs ⊚ p')) (λ q → σₛₙ (lvs (brs ⊚ p') ⊚ q)) ,
                 μ (σₙ , σₛₙ) U V (br (brs ⊚ p')) (λ q → ϕ (inr (p' , q)))

            where p' : Pos (Branch U) brs
                  p' = map-src-lift σₙ (Branch U) Q brs (λ p → σₛₙ (stm (brs ⊚ p))) p

  -- pairₚ : {n : ℕ} {𝑜 : 𝒪 n} 
  --   → (𝑝 : 𝒫 𝑜) (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → (p : Pos 𝑝) (q : Pos (𝑞 p))
  --   → Pos (μₒ 𝑝 𝑞)
  -- pairₚ objₒ 𝑠 p q = tt 
  -- pairₚ (ndₒ 𝑝 𝑞 𝑟) 𝑠 (inl tt) r =
  --   inlₒ (𝑠 (inl tt))
  --     (λ p → μₒ (𝑟 p) (λ q → 𝑠 (inr (p , q)))) r
  -- pairₚ (ndₒ 𝑝 𝑞 𝑟) 𝑠 (inr (p , q)) r =
  --   inrₒ (𝑠 (inl tt))
  --     (λ p → μₒ (𝑟 p) (λ q → 𝑠 (inr (p , q)))) p
  --       (pairₚ (𝑟 p) (λ q → 𝑠 (inr (p , q))) q r ) 

  -- fstₚ : {n : ℕ} {𝑜 : 𝒪 n} 
  --   → (𝑝 : 𝒫 𝑜) (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → Pos (μₒ 𝑝 𝑞) → Pos 𝑝
  -- fstₚ objₒ 𝑞 p = tt 
  -- fstₚ (ndₒ 𝑝 𝑞 𝑟) 𝑠 =
  --   graftₒ-pos-elim (𝑠 (inl tt)) (λ p → μₒ (𝑟 p) (λ q → 𝑠 (inr (p , q)))) _
  --     (const (inl tt)) (λ p q → inr (p , fstₚ (𝑟 p) (λ q → 𝑠 (inr (p , q))) q))

  -- sndₚ : {n : ℕ} {𝑜 : 𝒪 n} 
  --   → (𝑝 : 𝒫 𝑜) (𝑞 : (p : Pos 𝑝) → 𝒫 (Typ 𝑝 p))
  --   → (p : Pos (μₒ 𝑝 𝑞)) → Pos (𝑞 (fstₚ 𝑝 𝑞 p))
  -- sndₚ objₒ 𝑞 tt with 𝑞 tt 
  -- sndₚ objₒ 𝑞 tt | objₒ = tt 
  -- sndₚ (ndₒ 𝑝 𝑞 𝑟) 𝑠 =
  --   graftₒ-pos-elim (𝑠 (inl tt)) (λ p → μₒ (𝑟 p) (λ q → 𝑠 (inr (p , q)))) _
  --     (λ p → p) (λ p q → sndₚ (𝑟 p) (λ q → 𝑠 (inr (p , q))) q)
      
