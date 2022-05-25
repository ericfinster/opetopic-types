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

module Experimental.LessPositions.OpetopicType where

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
    → {P : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (p : Pos P s) → Frm X 

  _⊚_ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → {f : Frm X} (s : Src P f)
    → (p : Pos P s)
    → P (Typ s p)

  η : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (x : P f)
    → Src P f 

  η-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → (P : Frm X → Type ℓ)
    → {f : Frm X} (x : P f)
    → Pos P (η P x)

  μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (Q : Frm X → Type ℓ)
    → {f : Frm X} (s : Src P f)
    → (ϕ : (p : Pos P s) → Src Q (Typ s p))
    → Src Q f 

  postulate
  
    μ-pos : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos P s)
      → (q : Pos Q (ϕ p))
      → Pos Q (μ Q s ϕ) 

    μ-fst : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos Q (μ Q s ϕ))
      → Pos P s  

    μ-snd : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos Q (μ Q s ϕ))
      → Pos Q (ϕ (μ-fst s ϕ p))

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

    Typ-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos Q (μ Q s ϕ))
      → Typ (μ Q s ϕ) p ↦ Typ (ϕ (μ-fst s ϕ p)) (μ-snd s ϕ p)
    {-# REWRITE Typ-μ #-}

    ⊚-μ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos Q (μ Q s ϕ))
      → μ Q s ϕ ⊚ p ↦ ϕ (μ-fst s ϕ p) ⊚ μ-snd s ϕ p
    {-# REWRITE ⊚-μ #-}

    -- Laws for positions
    μ-fst-β : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → μ-fst s ϕ (μ-pos s ϕ p q) ↦ p 
    {-# REWRITE μ-fst-β #-}

    μ-snd-β : ∀ {n ℓ} {X : 𝕆Type n ℓ}
      → {P Q : Frm X → Type ℓ}
      → {f : Frm X} (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (p : Pos P s) (q : Pos Q (ϕ p))
      → μ-snd s ϕ (μ-pos s ϕ p q) ↦ q
    {-# REWRITE μ-snd-β #-}

    -- Monad Laws
    unit-left : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P Q : Frm X → Type ℓ)
      → (f : Frm X) (x : P f)
      → (ϕ : (p : Pos P (η P x)) → Src Q f)
      → μ Q (η P x) ϕ ↦ ϕ (η-pos P x)
    {-# REWRITE unit-left #-}
    
    unit-right : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → μ P s (λ p → η P (s ⊚ p)) ↦ s
    {-# REWRITE unit-right #-}
    
    μ-assoc : ∀ {n ℓ} (X : 𝕆Type n ℓ)
      → (P Q R : Frm X → Type ℓ)
      → (f : Frm X) (s : Src P f)
      → (ϕ : (p : Pos P s) → Src Q (Typ s p))
      → (ψ : (pq : Pos Q (μ Q s ϕ)) → Src R (Typ (μ Q s ϕ) pq))
      → μ R (μ Q s ϕ) ψ ↦ μ R s (λ p → μ R (ϕ p) (λ q → ψ (μ-pos s ϕ p q)))
    {-# REWRITE μ-assoc #-}

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
         → (flr : U (f , tgt , μ P brs (λ p → η P (stm (brs ⊚ p)))))
         → Pd (f , tgt , μ P brs (λ p → lvs (brs ⊚ p)))

  Src {zero} P _ = P tt*
  Src {suc n} U = Pd U

  Pos {zero} P s = Lift Unit
  Pos {suc n} U (lf tgt) = Lift ⊥
  Pos {suc n} U (nd tgt brs flr) =
    Unit ⊎ (Σ[ p ∈ Pos (Branch U) brs ]
            Pos U (br (brs ⊚ p)))

  Typ {zero} s p = tt*
  Typ {suc n} {X = X , P} {P = U} (nd tgt brs flr) (inl _) =
    _ , tgt , μ P brs (λ p → η P (stm (brs ⊚ p)))
  Typ {suc n} (nd tgt brs flr) (inr (p , q)) = Typ (br (brs ⊚ p)) q

  _⊚_ {zero} s p = s
  _⊚_ {suc n} (nd tgt brs flr) (inl _) = flr
  _⊚_ {suc n} (nd tgt brs flr) (inr (p , q)) = br (brs ⊚ p) ⊚ q

  η {zero} P x = x
  η {suc n} {X = X , P} U {f = f , t , s} x = 
    let brs = μ (Branch U) s (λ p → η (Branch U)
                [ s ⊚ p , η P (s ⊚ p) , lf (s ⊚ p) ])
    in nd t brs x
    
  η-pos {zero} P x = tt*
  η-pos {suc n} U x = inl tt

  γ : ∀ {n ℓ} {X : 𝕆Type n ℓ}
    → {P : Frm X → Type ℓ}
    → (U : Frm (X , P) → Type ℓ) 
    → {f : Frm X} (t : P f) (s : Src P f)
    → Pd U (f , t , s)
    → (ϕ : (p : Pos P s) → Σ[ lvs ∈ Src P (Typ s p) ]
                           Pd U (Typ s p , s ⊚ p , lvs))
    → Pd U (f , t , μ P s (λ p → fst (ϕ p)))
  γ U ._ ._ (lf tgt) ϕ = snd (ϕ (η-pos _ tgt))
  γ {P = P} U ._ ._ (nd tgt brs flr) ϕ =
    let -- ϕ' p q = ϕ (μ-pos brs (λ p' → lvs (brs ⊚ p')) p q)
    --     lvs' p = μ (lvs (brs ⊚ p)) (λ q → fst (ϕ' p q))
    --     br' p = γ U (stm (brs ⊚ p)) (lvs (brs ⊚ p)) (br (brs ⊚ p)) (ϕ' p)
    --     brs' = μ {Q = Branch U} brs
    --             (λ p → η {P = Branch U} [ stm' p , lvs' p , br' p ]) in
        brs' = μ (Branch U) brs (λ p → η (Branch U) [
                  stm (brs ⊚ p) ,
                  μ P (lvs (brs ⊚ p)) (λ q → fst (ϕ (μ-pos brs (λ p' → lvs (brs ⊚ p')) p q))) ,
                  γ U (stm (brs ⊚ p)) (lvs (brs ⊚ p)) (br (brs ⊚ p)) 
                     (λ q → (ϕ (μ-pos brs (λ p' → lvs (brs ⊚ p')) p q))) ])
                     
    in nd tgt brs' flr


  μ {zero} Q s ϕ = ϕ tt*
  μ {suc n} Q (lf tgt) ϕ = lf tgt
  μ {suc n} {X = X , P} {P = U₀} U (nd tgt brs flr) ϕ = 
    let w = ϕ (inl tt)
        δ p = η P (stm (brs ⊚ p))
    in γ U tgt (μ P brs δ) w
        (λ p → lvs (brs ⊚ (μ-fst brs δ p)) ,
               μ U (br (brs ⊚ (μ-fst brs δ p)))
                 (λ q → ϕ (inr (μ-fst brs δ p , q))))
                 
  -- Old version of μ
  μ' : ∀ {n ℓ} {Xₙ : 𝕆Type n ℓ} {Xₛₙ : Frm Xₙ → Type ℓ} {f : Frm Xₙ}
    → Src (Src Xₛₙ) f → Src Xₛₙ f
  μ' {Xₛₙ = Q} s = μ Q s (s ⊚_ )
