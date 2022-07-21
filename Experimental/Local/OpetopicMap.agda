{-# OPTIONS --no-termination-check #-}
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
open import Experimental.Local.OpetopicType

module Experimental.Local.OpetopicMap where

  --
  --  Maps of Opetopic Types
  --

  infixl 50 _⊙_

  _⇒_ : ∀ {n ℓ₀ ℓ₁} → 𝕆Type n ℓ₀ → 𝕆Type n ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)

  id-map : ∀ {n ℓ} → (X : 𝕆Type n ℓ) → X ⇒ X

  _⊙_ : ∀ {n ℓ₀ ℓ₁ ℓ₂} {X : 𝕆Type n ℓ₀}
    → {Y : 𝕆Type n ℓ₁} {Z : 𝕆Type n ℓ₂}
    → Y ⇒ Z → X ⇒ Y → X ⇒ Z


  Frm⇒ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → (σ : X ⇒ Y) → Frm X → Frm Y

  Src⇒ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → {P : Frm X → Type ℓ₀}
    → {Q : Frm Y → Type ℓ₁}
    → {f : Frm X} (s : Src P f) 
    → (σ : X ⇒ Y) (σ' : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
    → Src Q (Frm⇒ σ f)

  Pos⇒ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → {P : Frm X → Type ℓ₀}
    → {Q : Frm Y → Type ℓ₁}
    → {f : Frm X} (s : Src P f) 
    → (σ : X ⇒ Y) (σ' : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
    → Pos P s → Pos Q (Src⇒ s σ σ')

  Pos⇐ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → {P : Frm X → Type ℓ₀}
    → {Q : Frm Y → Type ℓ₁}
    → {f : Frm X} (s : Src P f) 
    → (σ : X ⇒ Y) (σ' : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
    → Pos Q (Src⇒ s σ σ') → Pos P s 

  postulate

    --
    --  Equations for maps
    -- 

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
    --  Typing and Inhabitants
    --

    Pos⇐-Typ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {f : Frm X} (s : Src P f) 
      → (σ : X ⇒ Y) (σ' : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (Src⇒ s σ σ'))
      → Typ Q (Src⇒ s σ σ') p ↦ Frm⇒ σ (Typ P s (Pos⇐ s σ σ' p))
    {-# REWRITE Pos⇐-Typ #-}

    Pos⇐-⊚ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {f : Frm X} (s : Src P f) 
      → (σ : X ⇒ Y) (σ' : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (Src⇒ s σ σ'))
      → Src⇒ s σ σ' ⊚ p ↦ σ' (Pos⇐ s σ σ' p) 
    {-# REWRITE Pos⇐-⊚ #-}

    --
    --  Pos β and η rules
    --

    Pos⇒-β : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {f : Frm X} (s : Src P f) 
      → (σ : X ⇒ Y) (σ' : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos P s)
      → Pos⇐ {Q = Q} s σ σ' (Pos⇒ {Q = Q} s σ σ' p) ↦ p 
    {-# REWRITE Pos⇒-β #-}

    Pos⇒-η : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {f : Frm X} (s : Src P f) 
      → (σ : X ⇒ Y) (σ' : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (p : Pos Q (Src⇒ s σ σ'))
      → Pos⇒ {Q = Q} s σ σ' (Pos⇐ {Q = Q} s σ σ' p) ↦ p 
    {-# REWRITE Pos⇒-η #-}

    --
    --  Frame compatibilities
    --
    
    Frm⇒-id : ∀ {n ℓ} (X : 𝕆Type n ℓ) (f : Frm X)
      → Frm⇒ (id-map X) f ↦ f
    {-# REWRITE Frm⇒-id #-}

    Frm⇒-⊙ : ∀ {n ℓ₀ ℓ₁ ℓ₂} {X : 𝕆Type n ℓ₀}
      → {Y : 𝕆Type n ℓ₁} {Z : 𝕆Type n ℓ₂}
      → (σ : X ⇒ Y) (τ : Y ⇒ Z) (f : Frm X)
      → Frm⇒ τ (Frm⇒ σ f) ↦ Frm⇒ (τ ⊙ σ) f 
    {-# REWRITE Frm⇒-⊙ #-}

    --
    --  Src compatibilities
    --

    Src⇒-id : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → Src⇒ {Q = P} s (id-map X) (λ p → s ⊚ p) ↦ s 
    {-# REWRITE Src⇒-id #-}

    Src⇒-⊙ : ∀ {n ℓ₀ ℓ₁ ℓ₂}
      → {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁} {Z : 𝕆Type n ℓ₂}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {R : Frm Z → Type ℓ₂}
      → {f : Frm X} (s : Src P f) 
      → (σ : X ⇒ Y) (σ' : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (τ : Y ⇒ Z) (τ' : (p : Pos Q (Src⇒ s σ σ')) → R (Frm⇒ τ (Typ Q (Src⇒ s σ σ') p)))
      → Src⇒ {Q = R} (Src⇒ s σ σ') τ τ' ↦
        Src⇒ {Q = R} s (τ ⊙ σ) (λ p → τ' (Pos⇒ s σ σ' p))
    {-# REWRITE Src⇒-⊙ #-} 

    Src⇒-ν : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {P Q : Frm X → Type ℓ₀}
      → {R : Frm Y → Type ℓ₁}
      → {f : Frm X} (s : Src P f) 
      → (ϕ : (p : Pos P s) → Q (Typ P s p))
      → (σ : X ⇒ Y) (σ' : (p : Pos Q (ν s ϕ)) → R (Frm⇒ σ (Typ Q (ν s ϕ) p)))
      → Src⇒ {Q = R} (ν s ϕ) σ σ' ↦ Src⇒ s σ (λ p → σ' (ν-pos s ϕ p))
    {-# REWRITE Src⇒-ν #-}

    Src⇒-η : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {f : Frm X} (x : P f) 
      → (σ : X ⇒ Y) (σ' : (p : Pos P (η P x)) → Q (Frm⇒ σ f))
      → Src⇒ (η P x) σ σ' ↦ η Q (σ' (η-pos P x))
    {-# REWRITE Src⇒-η #-}

    Src⇒-μ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {f : Frm X} (s : Src (Src P) f) 
      → (σ : X ⇒ Y) (σ' : (p : Pos P (μ P s)) → Q (Frm⇒ σ (Typ P (μ P s) p)))
      → Src⇒ (μ P s) σ σ' ↦ μ Q (Src⇒ s σ (λ p → Src⇒ (s ⊚ p) σ (λ q → σ' (μ-pos P s p q))))
    {-# REWRITE Src⇒-μ #-}
    
    ν-Src⇒ : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
      → {P : Frm X → Type ℓ₀}
      → {Q R : Frm Y → Type ℓ₁}
      → {f : Frm X} (s : Src P f)
      → (σ : X ⇒ Y) (σ' : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (ϕ : (p : Pos Q (Src⇒ s σ σ')) → R (Typ Q (Src⇒ s σ σ') p))
      → ν {Q = R} (Src⇒ s σ σ') ϕ ↦ Src⇒ s σ (λ p → ϕ (Pos⇒ s σ σ' p))
    {-# REWRITE ν-Src⇒ #-}


    --
    --  Position Compatibilities
    --

    Pos⇒-id : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → (p : Pos P s)
      → Pos⇒ {Q = P} s (id-map X) (λ p → s ⊚ p) p ↦ p
    {-# REWRITE Pos⇒-id #-}

    Pos⇒-⊙ : ∀ {n ℓ₀ ℓ₁ ℓ₂}
      → {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁} {Z : 𝕆Type n ℓ₂}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {R : Frm Z → Type ℓ₂}
      → {f : Frm X} (s : Src P f) 
      → (σ : X ⇒ Y) (σ' : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (τ : Y ⇒ Z) (τ' : (p : Pos Q (Src⇒ s σ σ')) → R (Frm⇒ τ (Typ Q (Src⇒ s σ σ') p)))
      → (p : Pos P s)
      → Pos⇒ {Q = R} (Src⇒ s σ σ') τ τ' (Pos⇒ s σ σ' p) ↦
          Pos⇒ {Q = R} s (τ ⊙ σ) (λ p → τ' (Pos⇒ s σ σ' p)) p
    {-# REWRITE Pos⇒-⊙ #-}

    Pos⇐-id : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → (p : Pos P s)
      → Pos⇐ {Q = P} s (id-map X) (λ p → s ⊚ p) p ↦ p 
    {-# REWRITE Pos⇐-id #-}
    
    Pos⇐-⊙ : ∀ {n ℓ₀ ℓ₁ ℓ₂}
      → {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁} {Z : 𝕆Type n ℓ₂}
      → {P : Frm X → Type ℓ₀}
      → {Q : Frm Y → Type ℓ₁}
      → {R : Frm Z → Type ℓ₂}
      → {f : Frm X} (s : Src P f) 
      → (σ : X ⇒ Y) (σ' : (p : Pos P s) → Q (Frm⇒ σ (Typ P s p)))
      → (τ : Y ⇒ Z) (τ' : (p : Pos Q (Src⇒ s σ σ')) → R (Frm⇒ τ (Typ Q (Src⇒ s σ σ') p)))
      → (p : Pos R (Src⇒ {Q = R} s (τ ⊙ σ) (λ p → τ' (Pos⇒ s σ σ' p))))
      → Pos⇐ {Q = Q} s σ σ' (Pos⇐ {Q = R} (Src⇒ s σ σ') τ τ' p) ↦
          Pos⇐ {Q = R} s (τ ⊙ σ) (λ p → τ' (Pos⇒ s σ σ' p)) p  
    {-# REWRITE Pos⇐-⊙ #-}


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
    Frm⇒ σₙ frm , Src⇒ src σₙ (λ p → σₛₙ (src ⊚ p)) , σₛₙ tgt

  Src⇒-brs : ∀ {n ℓ₀ ℓ₁} {X : 𝕆Type n ℓ₀} {Y : 𝕆Type n ℓ₁}
    → {P : Frm X → Type ℓ₀} {Q : Frm Y → Type ℓ₁}
    → {U : Frm (X , P) → Type ℓ₀} {V : Frm (Y , Q) → Type ℓ₁}
    → {f : Frm X} (src : Src P f) (tgt : P f) (flr : U (f , src , tgt))
    → (brs : Dec {P = P} (Branch U) src)
    → (σₙ : X ⇒ Y) (σₛₙ : {f : Frm X} → P f → Q (Frm⇒ σₙ f))
    → (σ' : (p : PdPos U (nd src tgt flr brs))
        → V (Frm⇒ (σₙ , σₛₙ) (Typ U (nd src tgt flr brs) p)))
    → (p : Pos Q (Src⇒ src σₙ (λ p₁ → σₛₙ (src ⊚ p₁))))
    → Branch V (σₛₙ (src ⊚ Pos⇐ src σₙ (λ p₁ → σₛₙ (src ⊚ p₁)) p))
  Src⇒-brs {X = X} {Y} {P} {Q} {U} {V} src tgt flr brs σₙ σₛₙ σ' p =
    let p' = Pos⇐ src σₙ (λ p₁ → σₛₙ (src ⊚ p₁)) p
    in [ Src⇒ (lvs (brs ⊛ p')) σₙ (λ q → σₛₙ (lvs (brs ⊛ p') ⊚ q))
       , Src⇒ {X = X , P} {Y = Y , Q} {P = U} {Q = V} (br (brs ⊛ p')) (σₙ , σₛₙ)
           (λ q → σ' (nd-there p' q)) ]

  Src⇒ {zero} σ σ' s = s tt*
  Src⇒ {suc n} {Q = Q} (lf tgt) (σₙ , σₛₙ) σ'  = lf (σₛₙ tgt)
  Src⇒ {suc n} {X = X , P} {Y = Y , Q} {P = U} {Q = V} (nd src tgt flr brs) (σₙ , σₛₙ) σ'  = 
    nd (Src⇒ src σₙ (λ p → σₛₙ (src ⊚ p))) (σₛₙ tgt) (σ' nd-here)
       (λ-dec {P = Q} (Branch V) (Src⇒ src σₙ (λ p → σₛₙ (src ⊚ p)))
                                 (Src⇒-brs src tgt flr brs σₙ σₛₙ σ')) 

  Pos⇒ {zero} s σ σ' p = tt*
  Pos⇒ {suc n} (nd src tgt flr brs) (σₙ , σₛₙ) σ' nd-here = nd-here
  Pos⇒ {suc n} (nd src tgt flr brs) (σₙ , σₛₙ) σ' (nd-there p q) =
    nd-there (Pos⇒ src σₙ (λ q → σₛₙ (src ⊚ q)) p)
             (Pos⇒ (br (brs ⊛ p)) (σₙ , σₛₙ) (λ q → σ' (nd-there p q)) q)
  
  Pos⇐ {zero} s σ σ' p = tt*
  Pos⇐ {suc n} (nd src tgt flr brs) (σₙ , σₛₙ) σ' nd-here = nd-here
  Pos⇐ {suc n} (nd src tgt flr brs) (σₙ , σₛₙ) σ' (nd-there p q) =
    let p' = Pos⇐ src σₙ (λ q → σₛₙ (src ⊚ q)) p
        q' = Pos⇐ (br (brs ⊛ p')) (σₙ , σₛₙ) (λ q → σ' (nd-there p' q)) q
    in nd-there p' q'

