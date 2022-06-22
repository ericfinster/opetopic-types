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

  map-pos↑ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
    → (P : Frm X → Type ℓ)
    → (Q : Frm Y → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
    → (p : Pos Q (map-src σ P Q s ϕ))
    → Pos P s
  map-pos↑ σ P Q s ϕ = μ-fst σ P Q s (λ p → η Q (ϕ p))  

  map-pos↓ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
    → (P : Frm X → Type ℓ)
    → (Q : Frm Y → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
    → (p : Pos P s)
    → Pos Q (map-src σ P Q s ϕ)
  map-pos↓ σ P Q s ϕ p = μ-pos σ P Q s (λ p → η Q (ϕ p)) p (η-pos Q (ϕ p))

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

    PdTyp : {f : Frm (X , P)} (pd : Pd f) → PdPos pd → Frm (X , P)
    PdTyp (nd tgt brs flr) (nd-here {f} {tgt} {brs}) = (f , μ (id-map X) Branch P brs (λ p → η P (stm (brs ⊚ p))) , tgt)
    PdTyp (nd tgt brs flr) (nd-there p q) = PdTyp (br (brs ⊚ p)) q

    PdInhab : {f : Frm (X , P)} (pd : Pd f) (p : PdPos pd) → U (PdTyp pd p)
    PdInhab (nd tgt brs flr) (nd-here {flr = flr}) = flr
    PdInhab (nd tgt brs flr) (nd-there p q) = PdInhab (br (brs ⊚ p)) q

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
          p' = map-pos↓ (id-map X) Branch Branch brs ψ p 
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
          p' = map-pos↓ (id-map X) Branch Branch brs ψ p 
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
          u' = map-pos↑ (id-map X) Branch Branch brs ψ u
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
  Pos {suc n} U pd = PdPos U pd 

  Typ {zero} P s p = tt*
  Typ {suc n} U pd p = PdTyp U pd p

  _⊚_ {zero} s p = s
  _⊚_ {suc n} {P = U} pd p = PdInhab U pd p

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
  η-pos {suc n} P x = nd-here

  η-pos-elim {zero} x Q q p = q
  η-pos-elim {suc n} x Q q nd-here = q

  μ {zero} {X = X} σ P Q s ϕ = ϕ tt*
  μ {suc n} {X = X , P} (σₙ , σₛₙ) U V (lf tgt) ϕ = lf (σₛₙ tgt)
  μ {suc n} {X = X , P} {Y , Q} (σₙ , σₛₙ) U V (nd {f} tgt brs flr) ϕ =
    let w = ϕ nd-here
        ϕ' p = let p' = map-pos↑ σₙ (Branch U) Q brs (λ p → σₛₙ (stm (brs ⊚ p))) p
               in map-src σₙ P Q (lvs (brs ⊚ p')) (λ q → σₛₙ (lvs (brs ⊚ p') ⊚ q)) ,
                 μ (σₙ , σₛₙ) U V (br (brs ⊚ p')) (λ q → ϕ (nd-there p' q))
    in γ V w ϕ'

  μ-pos {zero} σ P Q s ϕ p q = tt*
  μ-pos {suc n} {X = X , P} {Y , Q} (σₙ , σₛₙ) U V  (nd tgt brs flr) ϕ nd-here r = 
    let w = ϕ nd-here
        ϕ' p = let p' = map-pos↑ σₙ (Branch U) Q brs (λ p → σₛₙ (stm (brs ⊚ p))) p
               in map-src σₙ P Q (lvs (brs ⊚ p')) (λ q → σₛₙ (lvs (brs ⊚ p') ⊚ q)) ,
                 μ (σₙ , σₛₙ) U V (br (brs ⊚ p')) (λ q → ϕ (nd-there p' q))
    in γ-inl V w ϕ' r  
  μ-pos {suc n} {X = X , P} {Y , Q} (σₙ , σₛₙ) U V (nd tgt brs flr) ϕ (nd-there p q) r = 
    let w = ϕ nd-here
        ϕ' p = let p' = map-pos↑ σₙ (Branch U) Q brs (λ p → σₛₙ (stm (brs ⊚ p))) p
               in map-src σₙ P Q (lvs (brs ⊚ p')) (λ q → σₛₙ (lvs (brs ⊚ p') ⊚ q)) ,
                 μ (σₙ , σₛₙ) U V (br (brs ⊚ p')) (λ q → ϕ (nd-there p' q))
        p' = map-pos↓ σₙ (Branch U) Q brs (λ p → σₛₙ (stm (brs ⊚ p))) p
    in γ-inr V w ϕ' p' (μ-pos (σₙ , σₛₙ) U V (br (brs ⊚ p)) (λ q → ϕ (nd-there p q)) q r)

  μ-fst {zero} σ P Q s ϕ p = tt*
  μ-fst {suc n} {X = X , P} {Y = Y , Q} (σₙ , σₛₙ) U V (nd tgt brs flr) ϕ p =
    let w = ϕ nd-here
        ϕ' p = let p' = map-pos↑ σₙ (Branch U) Q brs (λ p → σₛₙ (stm (brs ⊚ p))) p
               in map-src σₙ P Q (lvs (brs ⊚ p')) (λ q → σₛₙ (lvs (brs ⊚ p') ⊚ q)) ,
                 μ (σₙ , σₛₙ) U V (br (brs ⊚ p')) (λ q → ϕ (nd-there p' q))
    in γ-pos-elim V w ϕ' (λ _ → PdPos U (nd tgt brs flr)) (λ p → nd-here)
        (λ p q → let p' = map-pos↑ σₙ (Branch U) Q brs (λ p → σₛₙ (stm (brs ⊚ p))) p
                 in nd-there p' (μ-fst (σₙ , σₛₙ) U V (br (brs ⊚ p')) (λ q → ϕ (nd-there p' q)) q)) p

  μ-snd {zero} σ P Q s ϕ p = tt*
  μ-snd {suc n} {X = X , P} {Y = Y , Q} (σₙ , σₛₙ) U V (nd tgt brs flr) ϕ p = 
    let w = ϕ nd-here
        ϕ' p = let p' = map-pos↑ σₙ (Branch U) Q brs (λ p → σₛₙ (stm (brs ⊚ p))) p
               in map-src σₙ P Q (lvs (brs ⊚ p')) (λ q → σₛₙ (lvs (brs ⊚ p') ⊚ q)) ,
                 μ (σₙ , σₛₙ) U V (br (brs ⊚ p')) (λ q → ϕ (nd-there p' q))
    in γ-pos-elim V w ϕ' (λ p → PdPos V (ϕ (μ-fst (σₙ , σₛₙ) U V (nd tgt brs flr) ϕ p)))
          (λ p → p) (λ p q → let p' = map-pos↑ σₙ (Branch U) Q brs (λ p → σₛₙ (stm (brs ⊚ p))) p
                             in μ-snd (σₙ , σₛₙ) U V (br (brs ⊚ p')) (λ q → ϕ (nd-there p' q)) q) p


  -- Useful definitions a posteriori
  Inhab : ∀ {n ℓ} {X : 𝕆Type n ℓ} (P : Frm X → Type ℓ) {f : Frm X} (s : Src P f) (p : Pos P s) → P (Typ P s p)
  Inhab {zero} P s p = s
  Inhab {suc n} P s p = PdInhab P s p

  Src⇒ : ∀ {n ℓ} {X Y : 𝕆Type n ℓ} (σ : X ⇒ Y)
    → (P : Frm X → Type ℓ)
    → (Q : Frm Y → Type ℓ)
    → ({f : Frm X} → P f → Q (Frm⇒ σ f))
    → {f : Frm X} (s : Src P f)
    → Src Q (Frm⇒ σ f)
  Src⇒ σ P Q σ' {f} s = map-src σ P Q s λ p → σ' (Inhab _ _ p)
